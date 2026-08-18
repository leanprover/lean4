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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object*, lean_object*);
lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_Platform_target;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedPackage_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 19, 111, 34, 42, 151, 87, 37)}};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedPackage_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__2;
static const lean_array_object l_Lake_instInhabitedPackage_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__4;
static const lean_string_object l_Lake_instInhabitedPackage_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__5 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__5_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__6;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__7;
static const lean_string_object l_Lake_instInhabitedPackage_default___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__8 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__8_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__9;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__10;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_instInhabitedPackage_default___closed__11;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_instInhabitedPackage_default___closed__12;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_instInhabitedPackage_default___closed__13;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__14;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackage_default;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackage;
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
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(lean_object* v_k_5_, lean_object* v_v_6_, lean_object* v_t_7_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
lean_object* v_size_8_; lean_object* v_k_9_; lean_object* v_v_10_; lean_object* v_l_11_; lean_object* v_r_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_292_; 
v_size_8_ = lean_ctor_get(v_t_7_, 0);
v_k_9_ = lean_ctor_get(v_t_7_, 1);
v_v_10_ = lean_ctor_get(v_t_7_, 2);
v_l_11_ = lean_ctor_get(v_t_7_, 3);
v_r_12_ = lean_ctor_get(v_t_7_, 4);
v_isSharedCheck_292_ = !lean_is_exclusive(v_t_7_);
if (v_isSharedCheck_292_ == 0)
{
v___x_14_ = v_t_7_;
v_isShared_15_ = v_isSharedCheck_292_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_r_12_);
lean_inc(v_l_11_);
lean_inc(v_v_10_);
lean_inc(v_k_9_);
lean_inc(v_size_8_);
lean_dec(v_t_7_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_292_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
uint8_t v___x_16_; 
v___x_16_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5_, v_k_9_);
switch(v___x_16_)
{
case 0:
{
lean_object* v_impl_17_; lean_object* v___x_18_; 
lean_dec(v_size_8_);
v_impl_17_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_5_, v_v_6_, v_l_11_);
v___x_18_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_12_) == 0)
{
lean_object* v_size_19_; lean_object* v_size_20_; lean_object* v_k_21_; lean_object* v_v_22_; lean_object* v_l_23_; lean_object* v_r_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_size_19_ = lean_ctor_get(v_r_12_, 0);
v_size_20_ = lean_ctor_get(v_impl_17_, 0);
lean_inc(v_size_20_);
v_k_21_ = lean_ctor_get(v_impl_17_, 1);
lean_inc(v_k_21_);
v_v_22_ = lean_ctor_get(v_impl_17_, 2);
lean_inc(v_v_22_);
v_l_23_ = lean_ctor_get(v_impl_17_, 3);
lean_inc(v_l_23_);
v_r_24_ = lean_ctor_get(v_impl_17_, 4);
lean_inc(v_r_24_);
v___x_25_ = lean_unsigned_to_nat(3u);
v___x_26_ = lean_nat_mul(v___x_25_, v_size_19_);
v___x_27_ = lean_nat_dec_lt(v___x_26_, v_size_20_);
lean_dec(v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
lean_dec(v_r_24_);
lean_dec(v_l_23_);
lean_dec(v_v_22_);
lean_dec(v_k_21_);
v___x_28_ = lean_nat_add(v___x_18_, v_size_20_);
lean_dec(v_size_20_);
v___x_29_ = lean_nat_add(v___x_28_, v_size_19_);
lean_dec(v___x_28_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 3, v_impl_17_);
lean_ctor_set(v___x_14_, 0, v___x_29_);
v___x_31_ = v___x_14_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_32_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_32_, 3, v_impl_17_);
lean_ctor_set(v_reuseFailAlloc_32_, 4, v_r_12_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
else
{
lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_98_; 
v_isSharedCheck_98_ = !lean_is_exclusive(v_impl_17_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; lean_object* v_unused_100_; lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_99_ = lean_ctor_get(v_impl_17_, 4);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v_impl_17_, 3);
lean_dec(v_unused_100_);
v_unused_101_ = lean_ctor_get(v_impl_17_, 2);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_impl_17_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_impl_17_, 0);
lean_dec(v_unused_103_);
v___x_34_ = v_impl_17_;
v_isShared_35_ = v_isSharedCheck_98_;
goto v_resetjp_33_;
}
else
{
lean_dec(v_impl_17_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_98_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_size_36_; lean_object* v_size_37_; lean_object* v_k_38_; lean_object* v_v_39_; lean_object* v_l_40_; lean_object* v_r_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_size_36_ = lean_ctor_get(v_l_23_, 0);
v_size_37_ = lean_ctor_get(v_r_24_, 0);
v_k_38_ = lean_ctor_get(v_r_24_, 1);
v_v_39_ = lean_ctor_get(v_r_24_, 2);
v_l_40_ = lean_ctor_get(v_r_24_, 3);
v_r_41_ = lean_ctor_get(v_r_24_, 4);
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lean_nat_mul(v___x_42_, v_size_36_);
v___x_44_ = lean_nat_dec_lt(v_size_37_, v___x_43_);
lean_dec(v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_73_; 
lean_inc(v_r_41_);
lean_inc(v_l_40_);
lean_inc(v_v_39_);
lean_inc(v_k_38_);
v_isSharedCheck_73_ = !lean_is_exclusive(v_r_24_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; lean_object* v_unused_75_; lean_object* v_unused_76_; lean_object* v_unused_77_; lean_object* v_unused_78_; 
v_unused_74_ = lean_ctor_get(v_r_24_, 4);
lean_dec(v_unused_74_);
v_unused_75_ = lean_ctor_get(v_r_24_, 3);
lean_dec(v_unused_75_);
v_unused_76_ = lean_ctor_get(v_r_24_, 2);
lean_dec(v_unused_76_);
v_unused_77_ = lean_ctor_get(v_r_24_, 1);
lean_dec(v_unused_77_);
v_unused_78_ = lean_ctor_get(v_r_24_, 0);
lean_dec(v_unused_78_);
v___x_46_ = v_r_24_;
v_isShared_47_ = v_isSharedCheck_73_;
goto v_resetjp_45_;
}
else
{
lean_dec(v_r_24_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_73_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___x_61_; lean_object* v___y_63_; 
v___x_48_ = lean_nat_add(v___x_18_, v_size_20_);
lean_dec(v_size_20_);
v___x_49_ = lean_nat_add(v___x_48_, v_size_19_);
lean_dec(v___x_48_);
v___x_61_ = lean_nat_add(v___x_18_, v_size_36_);
if (lean_obj_tag(v_l_40_) == 0)
{
lean_object* v_size_71_; 
v_size_71_ = lean_ctor_get(v_l_40_, 0);
lean_inc(v_size_71_);
v___y_63_ = v_size_71_;
goto v___jp_62_;
}
else
{
lean_object* v___x_72_; 
v___x_72_ = lean_unsigned_to_nat(0u);
v___y_63_ = v___x_72_;
goto v___jp_62_;
}
v___jp_50_:
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = lean_nat_add(v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec(v___y_52_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 4, v_r_12_);
lean_ctor_set(v___x_46_, 3, v_r_41_);
lean_ctor_set(v___x_46_, 2, v_v_10_);
lean_ctor_set(v___x_46_, 1, v_k_9_);
lean_ctor_set(v___x_46_, 0, v___x_54_);
v___x_56_ = v___x_46_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v_r_41_);
lean_ctor_set(v_reuseFailAlloc_60_, 4, v_r_12_);
v___x_56_ = v_reuseFailAlloc_60_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_58_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v___x_56_);
lean_ctor_set(v___x_34_, 3, v___y_51_);
lean_ctor_set(v___x_34_, 2, v_v_39_);
lean_ctor_set(v___x_34_, 1, v_k_38_);
lean_ctor_set(v___x_34_, 0, v___x_49_);
v___x_58_ = v___x_34_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_59_, 3, v___y_51_);
lean_ctor_set(v_reuseFailAlloc_59_, 4, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_nat_add(v___x_61_, v___y_63_);
lean_dec(v___y_63_);
lean_dec(v___x_61_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_l_40_);
lean_ctor_set(v___x_14_, 3, v_l_23_);
lean_ctor_set(v___x_14_, 2, v_v_22_);
lean_ctor_set(v___x_14_, 1, v_k_21_);
lean_ctor_set(v___x_14_, 0, v___x_64_);
v___x_66_ = v___x_14_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_k_21_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v_v_22_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v_l_23_);
lean_ctor_set(v_reuseFailAlloc_70_, 4, v_l_40_);
v___x_66_ = v_reuseFailAlloc_70_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_nat_add(v___x_18_, v_size_19_);
if (lean_obj_tag(v_r_41_) == 0)
{
lean_object* v_size_68_; 
v_size_68_ = lean_ctor_get(v_r_41_, 0);
lean_inc(v_size_68_);
v___y_51_ = v___x_66_;
v___y_52_ = v___x_67_;
v___y_53_ = v_size_68_;
goto v___jp_50_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___y_51_ = v___x_66_;
v___y_52_ = v___x_67_;
v___y_53_ = v___x_69_;
goto v___jp_50_;
}
}
}
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_del_object(v___x_14_);
v___x_79_ = lean_nat_add(v___x_18_, v_size_20_);
lean_dec(v_size_20_);
v___x_80_ = lean_nat_add(v___x_79_, v_size_19_);
lean_dec(v___x_79_);
v___x_81_ = lean_nat_add(v___x_18_, v_size_19_);
v___x_82_ = lean_nat_add(v___x_81_, v_size_37_);
lean_dec(v___x_81_);
lean_inc_ref(v_r_12_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_r_12_);
lean_ctor_set(v___x_34_, 3, v_r_24_);
lean_ctor_set(v___x_34_, 2, v_v_10_);
lean_ctor_set(v___x_34_, 1, v_k_9_);
lean_ctor_set(v___x_34_, 0, v___x_82_);
v___x_84_ = v___x_34_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_97_, 3, v_r_24_);
lean_ctor_set(v_reuseFailAlloc_97_, 4, v_r_12_);
v___x_84_ = v_reuseFailAlloc_97_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v_r_12_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; lean_object* v_unused_93_; lean_object* v_unused_94_; lean_object* v_unused_95_; lean_object* v_unused_96_; 
v_unused_92_ = lean_ctor_get(v_r_12_, 4);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_r_12_, 3);
lean_dec(v_unused_93_);
v_unused_94_ = lean_ctor_get(v_r_12_, 2);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_r_12_, 1);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_r_12_, 0);
lean_dec(v_unused_96_);
v___x_86_ = v_r_12_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_r_12_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 4, v___x_84_);
lean_ctor_set(v___x_86_, 3, v_l_23_);
lean_ctor_set(v___x_86_, 2, v_v_22_);
lean_ctor_set(v___x_86_, 1, v_k_21_);
lean_ctor_set(v___x_86_, 0, v___x_80_);
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_k_21_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v_v_22_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_l_23_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v___x_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_104_; 
v_l_104_ = lean_ctor_get(v_impl_17_, 3);
lean_inc(v_l_104_);
if (lean_obj_tag(v_l_104_) == 0)
{
lean_object* v_r_105_; lean_object* v_k_106_; lean_object* v_v_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v_r_105_ = lean_ctor_get(v_impl_17_, 4);
v_k_106_ = lean_ctor_get(v_impl_17_, 1);
v_v_107_ = lean_ctor_get(v_impl_17_, 2);
v_isSharedCheck_118_ = !lean_is_exclusive(v_impl_17_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; lean_object* v_unused_120_; 
v_unused_119_ = lean_ctor_get(v_impl_17_, 3);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_impl_17_, 0);
lean_dec(v_unused_120_);
v___x_109_ = v_impl_17_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_r_105_);
lean_inc(v_v_107_);
lean_inc(v_k_106_);
lean_dec(v_impl_17_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 3, v_r_105_);
lean_ctor_set(v___x_109_, 2, v_v_10_);
lean_ctor_set(v___x_109_, 1, v_k_9_);
lean_ctor_set(v___x_109_, 0, v___x_18_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_r_105_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v_r_105_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v___x_113_);
lean_ctor_set(v___x_14_, 3, v_l_104_);
lean_ctor_set(v___x_14_, 2, v_v_107_);
lean_ctor_set(v___x_14_, 1, v_k_106_);
lean_ctor_set(v___x_14_, 0, v___x_111_);
v___x_115_ = v___x_14_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_l_104_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_r_121_; 
v_r_121_ = lean_ctor_get(v_impl_17_, 4);
lean_inc(v_r_121_);
if (lean_obj_tag(v_r_121_) == 0)
{
lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_146_; 
v_k_122_ = lean_ctor_get(v_impl_17_, 1);
v_v_123_ = lean_ctor_get(v_impl_17_, 2);
v_isSharedCheck_146_ = !lean_is_exclusive(v_impl_17_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; lean_object* v_unused_148_; lean_object* v_unused_149_; 
v_unused_147_ = lean_ctor_get(v_impl_17_, 4);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_impl_17_, 3);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_impl_17_, 0);
lean_dec(v_unused_149_);
v___x_125_ = v_impl_17_;
v_isShared_126_ = v_isSharedCheck_146_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_v_123_);
lean_inc(v_k_122_);
lean_dec(v_impl_17_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_146_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_k_127_ = lean_ctor_get(v_r_121_, 1);
v_v_128_ = lean_ctor_get(v_r_121_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_r_121_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_143_ = lean_ctor_get(v_r_121_, 4);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_r_121_, 3);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_r_121_, 0);
lean_dec(v_unused_145_);
v___x_130_ = v_r_121_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_v_128_);
lean_inc(v_k_127_);
lean_dec(v_r_121_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(3u);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v_l_104_);
lean_ctor_set(v___x_130_, 3, v_l_104_);
lean_ctor_set(v___x_130_, 2, v_v_123_);
lean_ctor_set(v___x_130_, 1, v_k_122_);
lean_ctor_set(v___x_130_, 0, v___x_18_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_l_104_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_l_104_);
v___x_134_ = v_reuseFailAlloc_141_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_l_104_);
lean_ctor_set(v___x_125_, 2, v_v_10_);
lean_ctor_set(v___x_125_, 1, v_k_9_);
lean_ctor_set(v___x_125_, 0, v___x_18_);
v___x_136_ = v___x_125_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_l_104_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_l_104_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v___x_136_);
lean_ctor_set(v___x_14_, 3, v___x_134_);
lean_ctor_set(v___x_14_, 2, v_v_128_);
lean_ctor_set(v___x_14_, 1, v_k_127_);
lean_ctor_set(v___x_14_, 0, v___x_132_);
v___x_138_ = v___x_14_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(2u);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_r_121_);
lean_ctor_set(v___x_14_, 3, v_impl_17_);
lean_ctor_set(v___x_14_, 0, v___x_150_);
v___x_152_ = v___x_14_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_impl_17_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v_r_121_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
case 1:
{
lean_object* v___x_155_; 
lean_dec(v_v_10_);
lean_dec(v_k_9_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 2, v_v_6_);
lean_ctor_set(v___x_14_, 1, v_k_5_);
v___x_155_ = v___x_14_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_8_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_l_11_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_r_12_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
default: 
{
lean_object* v_impl_157_; lean_object* v___x_158_; 
lean_dec(v_size_8_);
v_impl_157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_5_, v_v_6_, v_r_12_);
v___x_158_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_11_) == 0)
{
lean_object* v_size_159_; lean_object* v_size_160_; lean_object* v_k_161_; lean_object* v_v_162_; lean_object* v_l_163_; lean_object* v_r_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_size_159_ = lean_ctor_get(v_l_11_, 0);
v_size_160_ = lean_ctor_get(v_impl_157_, 0);
lean_inc(v_size_160_);
v_k_161_ = lean_ctor_get(v_impl_157_, 1);
lean_inc(v_k_161_);
v_v_162_ = lean_ctor_get(v_impl_157_, 2);
lean_inc(v_v_162_);
v_l_163_ = lean_ctor_get(v_impl_157_, 3);
lean_inc(v_l_163_);
v_r_164_ = lean_ctor_get(v_impl_157_, 4);
lean_inc(v_r_164_);
v___x_165_ = lean_unsigned_to_nat(3u);
v___x_166_ = lean_nat_mul(v___x_165_, v_size_159_);
v___x_167_ = lean_nat_dec_lt(v___x_166_, v_size_160_);
lean_dec(v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec(v_r_164_);
lean_dec(v_l_163_);
lean_dec(v_v_162_);
lean_dec(v_k_161_);
v___x_168_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_169_ = lean_nat_add(v___x_168_, v_size_160_);
lean_dec(v_size_160_);
lean_dec(v___x_168_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_impl_157_);
lean_ctor_set(v___x_14_, 0, v___x_169_);
v___x_171_ = v___x_14_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_11_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_impl_157_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_237_ = lean_ctor_get(v_impl_157_, 4);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_impl_157_, 2);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_impl_157_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_241_);
v___x_174_ = v_impl_157_;
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
else
{
lean_dec(v_impl_157_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_size_176_; lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_l_179_; lean_object* v_r_180_; lean_object* v_size_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_size_176_ = lean_ctor_get(v_l_163_, 0);
v_k_177_ = lean_ctor_get(v_l_163_, 1);
v_v_178_ = lean_ctor_get(v_l_163_, 2);
v_l_179_ = lean_ctor_get(v_l_163_, 3);
v_r_180_ = lean_ctor_get(v_l_163_, 4);
v_size_181_ = lean_ctor_get(v_r_164_, 0);
v___x_182_ = lean_unsigned_to_nat(2u);
v___x_183_ = lean_nat_mul(v___x_182_, v_size_181_);
v___x_184_ = lean_nat_dec_lt(v_size_176_, v___x_183_);
lean_dec(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_212_; 
lean_inc(v_r_180_);
lean_inc(v_l_179_);
lean_inc(v_v_178_);
lean_inc(v_k_177_);
v_isSharedCheck_212_ = !lean_is_exclusive(v_l_163_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_213_ = lean_ctor_get(v_l_163_, 4);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_l_163_, 3);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_l_163_, 2);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_l_163_, 1);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_l_163_, 0);
lean_dec(v_unused_217_);
v___x_186_ = v_l_163_;
v_isShared_187_ = v_isSharedCheck_212_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_l_163_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_212_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_202_; 
v___x_188_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_189_ = lean_nat_add(v___x_188_, v_size_160_);
lean_dec(v_size_160_);
if (lean_obj_tag(v_l_179_) == 0)
{
lean_object* v_size_210_; 
v_size_210_ = lean_ctor_get(v_l_179_, 0);
lean_inc(v_size_210_);
v___y_202_ = v_size_210_;
goto v___jp_201_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___y_202_ = v___x_211_;
goto v___jp_201_;
}
v___jp_190_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_nat_add(v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec(v___y_192_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 4, v_r_164_);
lean_ctor_set(v___x_186_, 3, v_r_180_);
lean_ctor_set(v___x_186_, 2, v_v_162_);
lean_ctor_set(v___x_186_, 1, v_k_161_);
lean_ctor_set(v___x_186_, 0, v___x_194_);
v___x_196_ = v___x_186_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_161_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_162_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_r_180_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_r_164_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_196_);
lean_ctor_set(v___x_174_, 3, v___y_191_);
lean_ctor_set(v___x_174_, 2, v_v_178_);
lean_ctor_set(v___x_174_, 1, v_k_177_);
lean_ctor_set(v___x_174_, 0, v___x_189_);
v___x_198_ = v___x_174_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v___y_191_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_nat_add(v___x_188_, v___y_202_);
lean_dec(v___y_202_);
lean_dec(v___x_188_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_l_179_);
lean_ctor_set(v___x_14_, 0, v___x_203_);
v___x_205_ = v___x_14_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_l_11_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_l_179_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_nat_add(v___x_158_, v_size_181_);
if (lean_obj_tag(v_r_180_) == 0)
{
lean_object* v_size_207_; 
v_size_207_ = lean_ctor_get(v_r_180_, 0);
lean_inc(v_size_207_);
v___y_191_ = v___x_205_;
v___y_192_ = v___x_206_;
v___y_193_ = v_size_207_;
goto v___jp_190_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___y_191_ = v___x_205_;
v___y_192_ = v___x_206_;
v___y_193_ = v___x_208_;
goto v___jp_190_;
}
}
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_del_object(v___x_14_);
v___x_218_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_219_ = lean_nat_add(v___x_218_, v_size_160_);
lean_dec(v_size_160_);
v___x_220_ = lean_nat_add(v___x_218_, v_size_176_);
lean_dec(v___x_218_);
lean_inc_ref(v_l_11_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_l_163_);
lean_ctor_set(v___x_174_, 3, v_l_11_);
lean_ctor_set(v___x_174_, 2, v_v_10_);
lean_ctor_set(v___x_174_, 1, v_k_9_);
lean_ctor_set(v___x_174_, 0, v___x_220_);
v___x_222_ = v___x_174_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_11_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_l_163_);
v___x_222_ = v_reuseFailAlloc_235_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v_l_11_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_230_ = lean_ctor_get(v_l_11_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_l_11_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_l_11_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_l_11_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_l_11_, 0);
lean_dec(v_unused_234_);
v___x_224_ = v_l_11_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_l_11_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 4, v_r_164_);
lean_ctor_set(v___x_224_, 3, v___x_222_);
lean_ctor_set(v___x_224_, 2, v_v_162_);
lean_ctor_set(v___x_224_, 1, v_k_161_);
lean_ctor_set(v___x_224_, 0, v___x_219_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_161_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_162_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_r_164_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_242_; 
v_l_242_ = lean_ctor_get(v_impl_157_, 3);
lean_inc(v_l_242_);
if (lean_obj_tag(v_l_242_) == 0)
{
lean_object* v_r_243_; lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_268_; 
v_r_243_ = lean_ctor_get(v_impl_157_, 4);
v_k_244_ = lean_ctor_get(v_impl_157_, 1);
v_v_245_ = lean_ctor_get(v_impl_157_, 2);
v_isSharedCheck_268_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; 
v_unused_269_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_270_);
v___x_247_ = v_impl_157_;
v_isShared_248_ = v_isSharedCheck_268_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_r_243_);
lean_inc(v_v_245_);
lean_inc(v_k_244_);
lean_dec(v_impl_157_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_268_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_k_249_; lean_object* v_v_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_264_; 
v_k_249_ = lean_ctor_get(v_l_242_, 1);
v_v_250_ = lean_ctor_get(v_l_242_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_l_242_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_265_ = lean_ctor_get(v_l_242_, 4);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_l_242_, 3);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_l_242_, 0);
lean_dec(v_unused_267_);
v___x_252_ = v_l_242_;
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_v_250_);
lean_inc(v_k_249_);
lean_dec(v_l_242_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_243_, 2);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v_r_243_);
lean_ctor_set(v___x_252_, 3, v_r_243_);
lean_ctor_set(v___x_252_, 2, v_v_10_);
lean_ctor_set(v___x_252_, 1, v_k_9_);
lean_ctor_set(v___x_252_, 0, v___x_158_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_r_243_);
v___x_256_ = v_reuseFailAlloc_263_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
lean_inc(v_r_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 3, v_r_243_);
lean_ctor_set(v___x_247_, 0, v___x_158_);
v___x_258_ = v___x_247_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_244_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_245_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_r_243_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v___x_258_);
lean_ctor_set(v___x_14_, 3, v___x_256_);
lean_ctor_set(v___x_14_, 2, v_v_250_);
lean_ctor_set(v___x_14_, 1, v_k_249_);
lean_ctor_set(v___x_14_, 0, v___x_254_);
v___x_260_ = v___x_14_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
else
{
lean_object* v_r_271_; 
v_r_271_ = lean_ctor_get(v_impl_157_, 4);
lean_inc(v_r_271_);
if (lean_obj_tag(v_r_271_) == 0)
{
lean_object* v_k_272_; lean_object* v_v_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_k_272_ = lean_ctor_get(v_impl_157_, 1);
v_v_273_ = lean_ctor_get(v_impl_157_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_impl_157_, 4);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_287_);
v___x_275_ = v_impl_157_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_v_273_);
lean_inc(v_k_272_);
lean_dec(v_impl_157_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(3u);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v_l_242_);
lean_ctor_set(v___x_275_, 2, v_v_10_);
lean_ctor_set(v___x_275_, 1, v_k_9_);
lean_ctor_set(v___x_275_, 0, v___x_158_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_242_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_l_242_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_r_271_);
lean_ctor_set(v___x_14_, 3, v___x_279_);
lean_ctor_set(v___x_14_, 2, v_v_273_);
lean_ctor_set(v___x_14_, 1, v_k_272_);
lean_ctor_set(v___x_14_, 0, v___x_277_);
v___x_281_ = v___x_14_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_273_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_271_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(2u);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v_impl_157_);
lean_ctor_set(v___x_14_, 3, v_r_271_);
lean_ctor_set(v___x_14_, 0, v___x_288_);
v___x_290_ = v___x_14_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_r_271_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_impl_157_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
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
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_k_5_);
lean_ctor_set(v___x_294_, 2, v_v_6_);
lean_ctor_set(v___x_294_, 3, v_t_7_);
lean_ctor_set(v___x_294_, 4, v_t_7_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(lean_object* v_as_295_, size_t v_i_296_, size_t v_stop_297_, lean_object* v_b_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_eq(v_i_296_, v_stop_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v_name_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; 
v___x_300_ = lean_array_uget_borrowed(v_as_295_, v_i_296_);
v_name_301_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v___x_300_);
lean_inc(v_name_301_);
v___x_302_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_name_301_, v___x_300_, v_b_298_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_296_, v___x_303_);
v_i_296_ = v___x_304_;
v_b_298_ = v___x_302_;
goto _start;
}
else
{
return v_b_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1___boxed(lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_stop_308_, lean_object* v_b_309_){
_start:
{
size_t v_i_boxed_310_; size_t v_stop_boxed_311_; lean_object* v_res_312_; 
v_i_boxed_310_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_stop_boxed_311_ = lean_unbox_usize(v_stop_308_);
lean_dec(v_stop_308_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v_as_306_, v_i_boxed_310_, v_stop_boxed_311_, v_b_309_);
lean_dec_ref(v_as_306_);
return v_res_312_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
v___x_318_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_319_ = l_Lake_instInhabitedPackageConfig_default(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__4(void){
_start:
{
uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = 0;
v___x_323_ = lean_box(0);
v___x_324_ = l_Lean_Name_toString(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__6(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__5));
v___x_327_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__4, &l_Lake_instInhabitedPackage_default___closed__4_once, _init_l_Lake_instInhabitedPackage_default___closed__4);
v___x_328_ = lean_string_append(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__7(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_System_Platform_target;
v___x_330_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__6, &l_Lake_instInhabitedPackage_default___closed__6_once, _init_l_Lake_instInhabitedPackage_default___closed__6);
v___x_331_ = lean_string_append(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__9(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__8));
v___x_334_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__7, &l_Lake_instInhabitedPackage_default___closed__7_once, _init_l_Lake_instInhabitedPackage_default___closed__7);
v___x_335_ = lean_string_append(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__10(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_337_ = lean_array_get_size(v___x_336_);
return v___x_337_;
}
}
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__11(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_lt(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__12(void){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_342_ = lean_nat_dec_le(v___x_341_, v___x_341_);
return v___x_342_;
}
}
static size_t _init_l_Lake_instInhabitedPackage_default___closed__13(void){
_start:
{
lean_object* v___x_343_; size_t v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_344_ = lean_usize_of_nat(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__14(void){
_start:
{
lean_object* v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = lean_box(1);
v___x_346_ = lean_usize_once(&l_Lake_instInhabitedPackage_default___closed__13, &l_Lake_instInhabitedPackage_default___closed__13_once, _init_l_Lake_instInhabitedPackage_default___closed__13);
v___x_347_ = ((size_t)0ULL);
v___x_348_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v___x_348_, v___x_347_, v___x_346_, v___x_345_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_367_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_box(0);
v___x_352_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_353_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_354_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__2, &l_Lake_instInhabitedPackage_default___closed__2_once, _init_l_Lake_instInhabitedPackage_default___closed__2);
v___x_355_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_372_ = lean_box(1);
v___x_373_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__11, &l_Lake_instInhabitedPackage_default___closed__11_once, _init_l_Lake_instInhabitedPackage_default___closed__11);
if (v___x_373_ == 0)
{
v___y_367_ = v___x_372_;
goto v___jp_366_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__12, &l_Lake_instInhabitedPackage_default___closed__12_once, _init_l_Lake_instInhabitedPackage_default___closed__12);
if (v___x_374_ == 0)
{
if (v___x_373_ == 0)
{
v___y_367_ = v___x_372_;
goto v___jp_366_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_367_ = v___x_375_;
goto v___jp_366_;
}
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_367_ = v___x_376_;
goto v___jp_366_;
}
}
v___jp_356_:
{
lean_object* v_testDriver_363_; lean_object* v_lintDriver_364_; lean_object* v___x_365_; 
v_testDriver_363_ = lean_ctor_get(v___x_354_, 12);
v_lintDriver_364_ = lean_ctor_get(v___x_354_, 14);
lean_inc_ref(v_lintDriver_364_);
lean_inc_ref(v_testDriver_363_);
lean_inc_ref(v___y_362_);
lean_inc_ref(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_357_);
v___x_365_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v___x_365_, 0, v___x_350_);
lean_ctor_set(v___x_365_, 1, v___x_351_);
lean_ctor_set(v___x_365_, 2, v___x_352_);
lean_ctor_set(v___x_365_, 3, v___x_351_);
lean_ctor_set(v___x_365_, 4, v___x_353_);
lean_ctor_set(v___x_365_, 5, v___x_353_);
lean_ctor_set(v___x_365_, 6, v___x_354_);
lean_ctor_set(v___x_365_, 7, v___x_353_);
lean_ctor_set(v___x_365_, 8, v___x_353_);
lean_ctor_set(v___x_365_, 9, v___x_353_);
lean_ctor_set(v___x_365_, 10, v___x_353_);
lean_ctor_set(v___x_365_, 11, v___x_353_);
lean_ctor_set(v___x_365_, 12, v___x_355_);
lean_ctor_set(v___x_365_, 13, v___x_355_);
lean_ctor_set(v___x_365_, 14, v___x_355_);
lean_ctor_set(v___x_365_, 15, v___x_355_);
lean_ctor_set(v___x_365_, 16, v___y_357_);
lean_ctor_set(v___x_365_, 17, v___y_361_);
lean_ctor_set(v___x_365_, 18, v___y_360_);
lean_ctor_set(v___x_365_, 19, v___y_358_);
lean_ctor_set(v___x_365_, 20, v___y_359_);
lean_ctor_set(v___x_365_, 21, v___y_362_);
lean_ctor_set(v___x_365_, 22, v_testDriver_363_);
lean_ctor_set(v___x_365_, 23, v_lintDriver_364_);
return v___x_365_;
}
v___jp_366_:
{
lean_object* v_buildArchive_368_; lean_object* v___x_369_; 
v_buildArchive_368_ = lean_ctor_get(v___x_354_, 11);
v___x_369_ = lean_box(1);
if (lean_obj_tag(v_buildArchive_368_) == 1)
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v_buildArchive_368_, 0);
v___y_357_ = v___y_367_;
v___y_358_ = v___x_355_;
v___y_359_ = v___x_355_;
v___y_360_ = v___x_369_;
v___y_361_ = v___x_355_;
v___y_362_ = v_val_370_;
goto v___jp_356_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__9, &l_Lake_instInhabitedPackage_default___closed__9_once, _init_l_Lake_instInhabitedPackage_default___closed__9);
v___y_357_ = v___y_367_;
v___y_358_ = v___x_355_;
v___y_359_ = v___x_355_;
v___y_360_ = v___x_369_;
v___y_361_ = v___x_355_;
v___y_362_ = v___x_371_;
goto v___jp_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object* v_00_u03b2_377_, lean_object* v_k_378_, lean_object* v_v_379_, lean_object* v_t_380_, lean_object* v_hl_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_378_, v_v_379_, v_t_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lake_instInhabitedPackage_default;
return v___x_383_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_384_){
_start:
{
lean_object* v_keyName_385_; 
v_keyName_385_ = lean_ctor_get(v_pkg_384_, 2);
if (lean_obj_tag(v_keyName_385_) == 0)
{
uint64_t v___x_386_; 
v___x_386_ = 1723ULL;
return v___x_386_;
}
else
{
uint64_t v_hash_387_; 
v_hash_387_ = lean_ctor_get_uint64(v_keyName_385_, sizeof(void*)*2);
return v_hash_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_388_){
_start:
{
uint64_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lake_Package_instHashable___lam__0(v_pkg_388_);
lean_dec_ref(v_pkg_388_);
v_r_390_ = lean_box_uint64(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_393_, lean_object* v_p2_394_){
_start:
{
lean_object* v_wsIdx_395_; lean_object* v_wsIdx_396_; uint8_t v___x_397_; 
v_wsIdx_395_ = lean_ctor_get(v_p1_393_, 0);
v_wsIdx_396_ = lean_ctor_get(v_p2_394_, 0);
v___x_397_ = lean_nat_dec_eq(v_wsIdx_395_, v_wsIdx_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_398_, lean_object* v_p2_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lake_Package_instBEq___lam__0(v_p1_398_, v_p2_399_);
lean_dec_ref(v_p2_399_);
lean_dec_ref(v_p1_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_404_){
_start:
{
lean_object* v_baseName_405_; uint8_t v___x_406_; lean_object* v___x_407_; 
v_baseName_405_ = lean_ctor_get(v_self_404_, 1);
lean_inc(v_baseName_405_);
lean_dec_ref(v_self_404_);
v___x_406_ = 0;
v___x_407_ = l_Lean_Name_toString(v_baseName_405_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_408_){
_start:
{
lean_object* v_keyName_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_keyName_409_ = lean_ctor_get(v_x_408_, 2);
lean_inc(v_keyName_409_);
lean_dec_ref(v_x_408_);
v___x_410_ = 1;
v___x_411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_409_, v___x_410_);
v___x_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_415_){
_start:
{
lean_object* v_baseName_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v_baseName_416_ = lean_ctor_get(v_x_415_, 1);
lean_inc(v_baseName_416_);
lean_dec_ref(v_x_415_);
v___x_417_ = 0;
v___x_418_ = l_Lean_Name_toString(v_baseName_416_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_421_){
_start:
{
lean_object* v_baseName_422_; 
v_baseName_422_ = lean_ctor_get(v_self_421_, 1);
lean_inc(v_baseName_422_);
return v_baseName_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lake_Package_name(v_self_423_);
lean_dec_ref(v_self_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_425_){
_start:
{
lean_object* v_origName_426_; uint8_t v___x_427_; lean_object* v___x_428_; 
v_origName_426_ = lean_ctor_get(v_self_425_, 3);
lean_inc(v_origName_426_);
lean_dec_ref(v_self_425_);
v___x_427_ = 0;
v___x_428_ = l_Lean_Name_toString(v_origName_426_, v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_unsigned_to_nat(16u);
v___x_431_ = lean_mk_array(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_435_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___x_438_; 
v___f_436_ = ((lean_object*)(l_Lake_Package_instBEq___closed__0));
v___f_437_ = ((lean_object*)(l_Lake_Package_instHashable___closed__0));
v___x_438_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_437_, v___f_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object* v_self_440_){
_start:
{
lean_inc_ref(v_self_440_);
return v_self_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object* v_self_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_441_);
lean_dec_ref(v_self_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_444_){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___closed__0));
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_NPackage_instCoeOutPackage(v_n_446_);
lean_dec(v_n_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_448_){
_start:
{
lean_inc_ref(v_pkg_448_);
return v_pkg_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_449_);
lean_dec_ref(v_pkg_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_457_, v___y_458_, v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v_x_457_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_463_){
_start:
{
lean_object* v___f_464_; 
v___f_464_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_465_);
lean_dec(v_pkgName_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_467_){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lake_instInhabitedPostUpdateHook(v_a_469_);
lean_dec(v_a_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_471_){
_start:
{
lean_inc_ref(v_a_471_);
return v_a_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_472_);
lean_dec_ref(v_a_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_474_, lean_object* v_a_475_){
_start:
{
lean_inc_ref(v_a_475_);
return v_a_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_476_, v_a_477_);
lean_dec_ref(v_a_477_);
lean_dec(v_name_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_480_, 0, v_name_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_481_){
_start:
{
lean_inc(v_a_481_);
return v_a_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_482_);
lean_dec(v_a_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_484_, lean_object* v_a_485_){
_start:
{
lean_inc(v_a_485_);
return v_a_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec(v_name_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_490_, 0, v_name_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_491_){
_start:
{
lean_inc_ref(v_inst_491_);
return v_inst_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_492_);
lean_dec_ref(v_inst_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_494_, lean_object* v_inst_495_){
_start:
{
lean_inc_ref(v_inst_495_);
return v_inst_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_496_, v_inst_497_);
lean_dec_ref(v_inst_497_);
lean_dec(v_name_496_);
return v_res_498_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_506_){
_start:
{
lean_object* v_wsIdx_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_wsIdx_507_ = lean_ctor_get(v_self_506_, 0);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_nat_dec_eq(v_wsIdx_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Lake_Package_isRoot(v_self_510_);
lean_dec_ref(v_self_510_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_513_){
_start:
{
lean_object* v_config_514_; uint8_t v_bootstrap_515_; 
v_config_514_ = lean_ctor_get(v_self_513_, 6);
v_bootstrap_515_ = lean_ctor_get_uint8(v_config_514_, sizeof(void*)*27);
return v_bootstrap_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Lake_Package_bootstrap(v_self_516_);
lean_dec_ref(v_self_516_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_519_){
_start:
{
lean_object* v_config_520_; uint8_t v_bootstrap_521_; 
v_config_520_ = lean_ctor_get(v_self_519_, 6);
v_bootstrap_521_ = lean_ctor_get_uint8(v_config_520_, sizeof(void*)*27);
if (v_bootstrap_521_ == 0)
{
lean_object* v_origName_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_origName_522_ = lean_ctor_get(v_self_519_, 3);
lean_inc(v_origName_522_);
lean_dec_ref(v_self_519_);
v___x_523_ = l_Lean_Name_toString(v_origName_522_, v_bootstrap_521_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
lean_dec_ref(v_self_519_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_526_){
_start:
{
lean_object* v_config_527_; lean_object* v_version_528_; 
v_config_527_ = lean_ctor_get(v_self_526_, 6);
v_version_528_ = lean_ctor_get(v_config_527_, 16);
lean_inc_ref(v_version_528_);
return v_version_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lake_Package_version(v_self_529_);
lean_dec_ref(v_self_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_531_){
_start:
{
lean_object* v_config_532_; lean_object* v_versionTags_533_; 
v_config_532_ = lean_ctor_get(v_self_531_, 6);
v_versionTags_533_ = lean_ctor_get(v_config_532_, 17);
lean_inc_ref(v_versionTags_533_);
return v_versionTags_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_Package_versionTags(v_self_534_);
lean_dec_ref(v_self_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_536_){
_start:
{
lean_object* v_config_537_; lean_object* v_description_538_; 
v_config_537_ = lean_ctor_get(v_self_536_, 6);
v_description_538_ = lean_ctor_get(v_config_537_, 18);
lean_inc_ref(v_description_538_);
return v_description_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_Package_description(v_self_539_);
lean_dec_ref(v_self_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_541_){
_start:
{
lean_object* v_config_542_; lean_object* v_keywords_543_; 
v_config_542_ = lean_ctor_get(v_self_541_, 6);
v_keywords_543_ = lean_ctor_get(v_config_542_, 19);
lean_inc_ref(v_keywords_543_);
return v_keywords_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_Package_keywords(v_self_544_);
lean_dec_ref(v_self_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_546_){
_start:
{
lean_object* v_config_547_; lean_object* v_homepage_548_; 
v_config_547_ = lean_ctor_get(v_self_546_, 6);
v_homepage_548_ = lean_ctor_get(v_config_547_, 20);
lean_inc_ref(v_homepage_548_);
return v_homepage_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lake_Package_homepage(v_self_549_);
lean_dec_ref(v_self_549_);
return v_res_550_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_551_){
_start:
{
lean_object* v_config_552_; uint8_t v_reservoir_553_; 
v_config_552_ = lean_ctor_get(v_self_551_, 6);
v_reservoir_553_ = lean_ctor_get_uint8(v_config_552_, sizeof(void*)*27 + 3);
return v_reservoir_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lake_Package_reservoir(v_self_554_);
lean_dec_ref(v_self_554_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_557_){
_start:
{
lean_object* v_config_558_; lean_object* v_license_559_; 
v_config_558_ = lean_ctor_get(v_self_557_, 6);
v_license_559_ = lean_ctor_get(v_config_558_, 21);
lean_inc_ref(v_license_559_);
return v_license_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_Package_license(v_self_560_);
lean_dec_ref(v_self_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_582_){
_start:
{
lean_object* v_config_583_; lean_object* v_licenseFiles_584_; lean_object* v___f_585_; lean_object* v___x_586_; size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; 
v_config_583_ = lean_ctor_get(v_self_582_, 6);
lean_inc_ref(v_config_583_);
lean_dec_ref(v_self_582_);
v_licenseFiles_584_ = lean_ctor_get(v_config_583_, 22);
lean_inc_ref(v_licenseFiles_584_);
lean_dec_ref(v_config_583_);
v___f_585_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_586_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_587_ = lean_array_size(v_licenseFiles_584_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_586_, v___f_585_, v_sz_587_, v___x_588_, v_licenseFiles_584_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = l_System_FilePath_normalize(v_x_591_);
v___x_593_ = l_Lake_joinRelative(v_dir_590_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_594_){
_start:
{
lean_object* v_config_595_; lean_object* v_dir_596_; lean_object* v_licenseFiles_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; size_t v_sz_601_; size_t v___x_602_; lean_object* v___x_603_; size_t v_sz_604_; lean_object* v___x_605_; 
v_config_595_ = lean_ctor_get(v_self_594_, 6);
lean_inc_ref(v_config_595_);
v_dir_596_ = lean_ctor_get(v_self_594_, 4);
lean_inc_ref(v_dir_596_);
lean_dec_ref(v_self_594_);
v_licenseFiles_597_ = lean_ctor_get(v_config_595_, 22);
lean_inc_ref(v_licenseFiles_597_);
lean_dec_ref(v_config_595_);
v___f_598_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_599_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_599_, 0, v_dir_596_);
v___x_600_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_601_ = lean_array_size(v_licenseFiles_597_);
v___x_602_ = ((size_t)0ULL);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_600_, v___f_598_, v_sz_601_, v___x_602_, v_licenseFiles_597_);
v_sz_604_ = lean_array_size(v___x_603_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_600_, v___f_599_, v_sz_604_, v___x_602_, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_606_){
_start:
{
lean_object* v_config_607_; lean_object* v_readmeFile_608_; lean_object* v___x_609_; 
v_config_607_ = lean_ctor_get(v_self_606_, 6);
lean_inc_ref(v_config_607_);
lean_dec_ref(v_self_606_);
v_readmeFile_608_ = lean_ctor_get(v_config_607_, 23);
lean_inc_ref(v_readmeFile_608_);
lean_dec_ref(v_config_607_);
v___x_609_ = l_System_FilePath_normalize(v_readmeFile_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_610_){
_start:
{
lean_object* v_config_611_; lean_object* v_dir_612_; lean_object* v_readmeFile_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_config_611_ = lean_ctor_get(v_self_610_, 6);
lean_inc_ref(v_config_611_);
v_dir_612_ = lean_ctor_get(v_self_610_, 4);
lean_inc_ref(v_dir_612_);
lean_dec_ref(v_self_610_);
v_readmeFile_613_ = lean_ctor_get(v_config_611_, 23);
lean_inc_ref(v_readmeFile_613_);
lean_dec_ref(v_config_611_);
v___x_614_ = l_System_FilePath_normalize(v_readmeFile_613_);
v___x_615_ = l_Lake_joinRelative(v_dir_612_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lake_defaultLakeDir;
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lake_Package_relLakeDir(v_x_618_);
lean_dec_ref(v_x_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_620_){
_start:
{
lean_object* v_dir_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_dir_621_ = lean_ctor_get(v_self_620_, 4);
lean_inc_ref(v_dir_621_);
lean_dec_ref(v_self_620_);
v___x_622_ = l_Lake_defaultLakeDir;
v___x_623_ = l_Lake_joinRelative(v_dir_621_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_624_){
_start:
{
lean_object* v_config_625_; lean_object* v_toWorkspaceConfig_626_; lean_object* v___x_627_; 
v_config_625_ = lean_ctor_get(v_self_624_, 6);
lean_inc_ref(v_config_625_);
lean_dec_ref(v_self_624_);
v_toWorkspaceConfig_626_ = lean_ctor_get(v_config_625_, 0);
lean_inc_ref(v_toWorkspaceConfig_626_);
lean_dec_ref(v_config_625_);
v___x_627_ = l_System_FilePath_normalize(v_toWorkspaceConfig_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_628_){
_start:
{
lean_object* v_config_629_; lean_object* v_dir_630_; lean_object* v_toWorkspaceConfig_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_config_629_ = lean_ctor_get(v_self_628_, 6);
lean_inc_ref(v_config_629_);
v_dir_630_ = lean_ctor_get(v_self_628_, 4);
lean_inc_ref(v_dir_630_);
lean_dec_ref(v_self_628_);
v_toWorkspaceConfig_631_ = lean_ctor_get(v_config_629_, 0);
lean_inc_ref(v_toWorkspaceConfig_631_);
lean_dec_ref(v_config_629_);
v___x_632_ = l_System_FilePath_normalize(v_toWorkspaceConfig_631_);
v___x_633_ = l_Lake_joinRelative(v_dir_630_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_634_){
_start:
{
lean_object* v_dir_635_; lean_object* v_relManifestFile_636_; lean_object* v___x_637_; 
v_dir_635_ = lean_ctor_get(v_self_634_, 4);
lean_inc_ref(v_dir_635_);
v_relManifestFile_636_ = lean_ctor_get(v_self_634_, 9);
lean_inc_ref(v_relManifestFile_636_);
lean_dec_ref(v_self_634_);
v___x_637_ = l_Lake_joinRelative(v_dir_635_, v_relManifestFile_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_638_){
_start:
{
lean_object* v_config_639_; lean_object* v_dir_640_; lean_object* v_buildDir_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_config_639_ = lean_ctor_get(v_self_638_, 6);
lean_inc_ref(v_config_639_);
v_dir_640_ = lean_ctor_get(v_self_638_, 4);
lean_inc_ref(v_dir_640_);
lean_dec_ref(v_self_638_);
v_buildDir_641_ = lean_ctor_get(v_config_639_, 5);
lean_inc_ref(v_buildDir_641_);
lean_dec_ref(v_config_639_);
v___x_642_ = l_System_FilePath_normalize(v_buildDir_641_);
v___x_643_ = l_Lake_joinRelative(v_dir_640_, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_644_){
_start:
{
lean_object* v_config_645_; lean_object* v_testDriverArgs_646_; 
v_config_645_ = lean_ctor_get(v_self_644_, 6);
v_testDriverArgs_646_ = lean_ctor_get(v_config_645_, 13);
lean_inc_ref(v_testDriverArgs_646_);
return v_testDriverArgs_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lake_Package_testDriverArgs(v_self_647_);
lean_dec_ref(v_self_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_649_){
_start:
{
lean_object* v_config_650_; lean_object* v_lintDriverArgs_651_; 
v_config_650_ = lean_ctor_get(v_self_649_, 6);
v_lintDriverArgs_651_ = lean_ctor_get(v_config_650_, 15);
lean_inc_ref(v_lintDriverArgs_651_);
return v_lintDriverArgs_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lake_Package_lintDriverArgs(v_self_652_);
lean_dec_ref(v_self_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_654_){
_start:
{
lean_object* v_config_655_; lean_object* v_extraDepTargets_656_; 
v_config_655_ = lean_ctor_get(v_self_654_, 6);
v_extraDepTargets_656_ = lean_ctor_get(v_config_655_, 2);
lean_inc_ref(v_extraDepTargets_656_);
return v_extraDepTargets_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lake_Package_extraDepTargets(v_self_657_);
lean_dec_ref(v_self_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_659_){
_start:
{
lean_object* v_config_660_; lean_object* v_toLeanConfig_661_; lean_object* v_platformIndependent_662_; 
v_config_660_ = lean_ctor_get(v_self_659_, 6);
v_toLeanConfig_661_ = lean_ctor_get(v_config_660_, 1);
v_platformIndependent_662_ = lean_ctor_get(v_toLeanConfig_661_, 10);
lean_inc(v_platformIndependent_662_);
return v_platformIndependent_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_Package_platformIndependent(v_self_663_);
lean_dec_ref(v_self_663_);
return v_res_664_;
}
}
static lean_object* _init_l_Lake_Package_isPlatformIndependent___closed__0(void){
_start:
{
lean_object* v___x_665_; lean_object* v___f_666_; 
v___x_665_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_666_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_666_, 0, v___x_665_);
return v___f_666_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_670_){
_start:
{
lean_object* v_config_671_; lean_object* v_toLeanConfig_672_; lean_object* v_platformIndependent_673_; lean_object* v___f_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_config_671_ = lean_ctor_get(v_self_670_, 6);
lean_inc_ref(v_config_671_);
lean_dec_ref(v_self_670_);
v_toLeanConfig_672_ = lean_ctor_get(v_config_671_, 1);
lean_inc_ref(v_toLeanConfig_672_);
lean_dec_ref(v_config_671_);
v_platformIndependent_673_ = lean_ctor_get(v_toLeanConfig_672_, 10);
lean_inc(v_platformIndependent_673_);
lean_dec_ref(v_toLeanConfig_672_);
v___f_674_ = lean_obj_once(&l_Lake_Package_isPlatformIndependent___closed__0, &l_Lake_Package_isPlatformIndependent___closed__0_once, _init_l_Lake_Package_isPlatformIndependent___closed__0);
v___x_675_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_676_ = l_Option_instBEq_beq___redArg(v___f_674_, v_platformIndependent_673_, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lake_Package_isPlatformIndependent(v_self_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_680_){
_start:
{
lean_object* v_config_681_; uint8_t v_fixedToolchain_682_; 
v_config_681_ = lean_ctor_get(v_self_680_, 6);
v_fixedToolchain_682_ = lean_ctor_get_uint8(v_config_681_, sizeof(void*)*27 + 6);
return v_fixedToolchain_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Lake_Package_fixedToolchain(v_self_683_);
lean_dec_ref(v_self_683_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_686_){
_start:
{
lean_object* v_config_687_; lean_object* v_releaseRepo_688_; 
v_config_687_ = lean_ctor_get(v_self_686_, 6);
v_releaseRepo_688_ = lean_ctor_get(v_config_687_, 10);
lean_inc(v_releaseRepo_688_);
return v_releaseRepo_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lake_Package_releaseRepo_x3f(v_self_689_);
lean_dec_ref(v_self_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_691_){
_start:
{
lean_object* v_remoteUrl_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_remoteUrl_692_ = lean_ctor_get(v_self_691_, 11);
v___x_693_ = lean_string_utf8_byte_size(v_remoteUrl_692_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_nat_dec_eq(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_inc_ref(v_remoteUrl_692_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_remoteUrl_692_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lake_Package_remoteUrl_x3f(v_self_698_);
lean_dec_ref(v_self_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_700_){
_start:
{
lean_object* v_dir_701_; lean_object* v_buildArchive_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_dir_701_ = lean_ctor_get(v_self_700_, 4);
lean_inc_ref(v_dir_701_);
v_buildArchive_702_ = lean_ctor_get(v_self_700_, 21);
lean_inc_ref(v_buildArchive_702_);
lean_dec_ref(v_self_700_);
v___x_703_ = l_Lake_defaultLakeDir;
v___x_704_ = l_Lake_joinRelative(v_dir_701_, v___x_703_);
v___x_705_ = l_Lake_joinRelative(v___x_704_, v_buildArchive_702_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_707_){
_start:
{
lean_object* v_dir_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_dir_708_ = lean_ctor_get(v_self_707_, 4);
lean_inc_ref(v_dir_708_);
lean_dec_ref(v_self_707_);
v___x_709_ = l_Lake_defaultLakeDir;
v___x_710_ = l_Lake_joinRelative(v_dir_708_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_712_ = l_Lake_joinRelative(v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_713_){
_start:
{
lean_object* v_config_714_; uint8_t v_preferReleaseBuild_715_; 
v_config_714_ = lean_ctor_get(v_self_713_, 6);
v_preferReleaseBuild_715_ = lean_ctor_get_uint8(v_config_714_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lake_Package_preferReleaseBuild(v_self_716_);
lean_dec_ref(v_self_716_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_719_){
_start:
{
lean_object* v_config_720_; uint8_t v_precompileModules_721_; 
v_config_720_ = lean_ctor_get(v_self_719_, 6);
v_precompileModules_721_ = lean_ctor_get_uint8(v_config_720_, sizeof(void*)*27 + 1);
return v_precompileModules_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Lake_Package_precompileModules(v_self_722_);
lean_dec_ref(v_self_722_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_725_){
_start:
{
lean_object* v_config_726_; lean_object* v_moreGlobalServerArgs_727_; 
v_config_726_ = lean_ctor_get(v_self_725_, 6);
v_moreGlobalServerArgs_727_ = lean_ctor_get(v_config_726_, 3);
lean_inc_ref(v_moreGlobalServerArgs_727_);
return v_moreGlobalServerArgs_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lake_Package_moreGlobalServerArgs(v_self_728_);
lean_dec_ref(v_self_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_730_){
_start:
{
lean_object* v_config_731_; lean_object* v_toLeanConfig_732_; lean_object* v_leanOptions_733_; lean_object* v_moreServerOptions_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_config_731_ = lean_ctor_get(v_self_730_, 6);
v_toLeanConfig_732_ = lean_ctor_get(v_config_731_, 1);
v_leanOptions_733_ = lean_ctor_get(v_toLeanConfig_732_, 0);
v_moreServerOptions_734_ = lean_ctor_get(v_toLeanConfig_732_, 4);
v___x_735_ = l_Lean_LeanOptions_ofArray(v_leanOptions_733_);
v___x_736_ = l_Lean_LeanOptions_appendArray(v___x_735_, v_moreServerOptions_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_Package_moreServerOptions(v_self_737_);
lean_dec_ref(v_self_737_);
return v_res_738_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_739_){
_start:
{
lean_object* v_config_740_; lean_object* v_toLeanConfig_741_; uint8_t v_buildType_742_; 
v_config_740_ = lean_ctor_get(v_self_739_, 6);
v_toLeanConfig_741_ = lean_ctor_get(v_config_740_, 1);
v_buildType_742_ = lean_ctor_get_uint8(v_toLeanConfig_741_, sizeof(void*)*13);
return v_buildType_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Lake_Package_buildType(v_self_743_);
lean_dec_ref(v_self_743_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_746_){
_start:
{
lean_object* v_config_747_; lean_object* v_toLeanConfig_748_; uint8_t v_backend_749_; 
v_config_747_ = lean_ctor_get(v_self_746_, 6);
v_toLeanConfig_748_ = lean_ctor_get(v_config_747_, 1);
v_backend_749_ = lean_ctor_get_uint8(v_toLeanConfig_748_, sizeof(void*)*13 + 1);
return v_backend_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Lake_Package_backend(v_self_750_);
lean_dec_ref(v_self_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_753_){
_start:
{
lean_object* v_config_754_; uint8_t v_allowImportAll_755_; 
v_config_754_ = lean_ctor_get(v_self_753_, 6);
v_allowImportAll_755_ = lean_ctor_get_uint8(v_config_754_, sizeof(void*)*27 + 5);
return v_allowImportAll_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Lake_Package_allowImportAll(v_self_756_);
lean_dec_ref(v_self_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_759_){
_start:
{
lean_object* v_config_760_; lean_object* v_toLeanConfig_761_; uint8_t v_requiresModuleSystem_762_; 
v_config_760_ = lean_ctor_get(v_self_759_, 6);
v_toLeanConfig_761_ = lean_ctor_get(v_config_760_, 1);
v_requiresModuleSystem_762_ = lean_ctor_get_uint8(v_toLeanConfig_761_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lake_Package_requiresModuleSystem(v_self_763_);
lean_dec_ref(v_self_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_766_){
_start:
{
lean_object* v_config_767_; lean_object* v_toLeanConfig_768_; uint8_t v_allowNonModules_769_; 
v_config_767_ = lean_ctor_get(v_self_766_, 6);
v_toLeanConfig_768_ = lean_ctor_get(v_config_767_, 1);
v_allowNonModules_769_ = lean_ctor_get_uint8(v_toLeanConfig_768_, sizeof(void*)*13 + 3);
return v_allowNonModules_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lake_Package_allowNonModules(v_self_770_);
lean_dec_ref(v_self_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_773_){
_start:
{
lean_object* v_config_774_; lean_object* v_toLeanConfig_775_; lean_object* v_dynlibs_776_; 
v_config_774_ = lean_ctor_get(v_self_773_, 6);
v_toLeanConfig_775_ = lean_ctor_get(v_config_774_, 1);
v_dynlibs_776_ = lean_ctor_get(v_toLeanConfig_775_, 11);
lean_inc_ref(v_dynlibs_776_);
return v_dynlibs_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lake_Package_dynlibs(v_self_777_);
lean_dec_ref(v_self_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_779_){
_start:
{
lean_object* v_config_780_; lean_object* v_toLeanConfig_781_; lean_object* v_plugins_782_; 
v_config_780_ = lean_ctor_get(v_self_779_, 6);
v_toLeanConfig_781_ = lean_ctor_get(v_config_780_, 1);
v_plugins_782_ = lean_ctor_get(v_toLeanConfig_781_, 12);
lean_inc_ref(v_plugins_782_);
return v_plugins_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lake_Package_plugins(v_self_783_);
lean_dec_ref(v_self_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_785_){
_start:
{
lean_object* v_config_786_; lean_object* v_toLeanConfig_787_; lean_object* v_leanOptions_788_; lean_object* v___x_789_; 
v_config_786_ = lean_ctor_get(v_self_785_, 6);
v_toLeanConfig_787_ = lean_ctor_get(v_config_786_, 1);
v_leanOptions_788_ = lean_ctor_get(v_toLeanConfig_787_, 0);
v___x_789_ = l_Lean_LeanOptions_ofArray(v_leanOptions_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_Package_leanOptions(v_self_790_);
lean_dec_ref(v_self_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_792_){
_start:
{
lean_object* v_config_793_; lean_object* v_toLeanConfig_794_; lean_object* v_moreLeanArgs_795_; 
v_config_793_ = lean_ctor_get(v_self_792_, 6);
v_toLeanConfig_794_ = lean_ctor_get(v_config_793_, 1);
v_moreLeanArgs_795_ = lean_ctor_get(v_toLeanConfig_794_, 1);
lean_inc_ref(v_moreLeanArgs_795_);
return v_moreLeanArgs_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lake_Package_moreLeanArgs(v_self_796_);
lean_dec_ref(v_self_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_798_){
_start:
{
lean_object* v_config_799_; lean_object* v_toLeanConfig_800_; lean_object* v_weakLeanArgs_801_; 
v_config_799_ = lean_ctor_get(v_self_798_, 6);
v_toLeanConfig_800_ = lean_ctor_get(v_config_799_, 1);
v_weakLeanArgs_801_ = lean_ctor_get(v_toLeanConfig_800_, 2);
lean_inc_ref(v_weakLeanArgs_801_);
return v_weakLeanArgs_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lake_Package_weakLeanArgs(v_self_802_);
lean_dec_ref(v_self_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_804_){
_start:
{
lean_object* v_config_805_; lean_object* v_toLeanConfig_806_; lean_object* v_moreLeancArgs_807_; 
v_config_805_ = lean_ctor_get(v_self_804_, 6);
v_toLeanConfig_806_ = lean_ctor_get(v_config_805_, 1);
v_moreLeancArgs_807_ = lean_ctor_get(v_toLeanConfig_806_, 3);
lean_inc_ref(v_moreLeancArgs_807_);
return v_moreLeancArgs_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lake_Package_moreLeancArgs(v_self_808_);
lean_dec_ref(v_self_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_810_){
_start:
{
lean_object* v_config_811_; lean_object* v_toLeanConfig_812_; lean_object* v_weakLeancArgs_813_; 
v_config_811_ = lean_ctor_get(v_self_810_, 6);
v_toLeanConfig_812_ = lean_ctor_get(v_config_811_, 1);
v_weakLeancArgs_813_ = lean_ctor_get(v_toLeanConfig_812_, 5);
lean_inc_ref(v_weakLeancArgs_813_);
return v_weakLeancArgs_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lake_Package_weakLeancArgs(v_self_814_);
lean_dec_ref(v_self_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_816_){
_start:
{
lean_object* v_config_817_; lean_object* v_toLeanConfig_818_; lean_object* v_moreLinkObjs_819_; 
v_config_817_ = lean_ctor_get(v_self_816_, 6);
v_toLeanConfig_818_ = lean_ctor_get(v_config_817_, 1);
v_moreLinkObjs_819_ = lean_ctor_get(v_toLeanConfig_818_, 6);
lean_inc_ref(v_moreLinkObjs_819_);
return v_moreLinkObjs_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lake_Package_moreLinkObjs(v_self_820_);
lean_dec_ref(v_self_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_822_){
_start:
{
lean_object* v_config_823_; lean_object* v_toLeanConfig_824_; lean_object* v_moreLinkLibs_825_; 
v_config_823_ = lean_ctor_get(v_self_822_, 6);
v_toLeanConfig_824_ = lean_ctor_get(v_config_823_, 1);
v_moreLinkLibs_825_ = lean_ctor_get(v_toLeanConfig_824_, 7);
lean_inc_ref(v_moreLinkLibs_825_);
return v_moreLinkLibs_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lake_Package_moreLinkLibs(v_self_826_);
lean_dec_ref(v_self_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_828_){
_start:
{
lean_object* v_config_829_; lean_object* v_toLeanConfig_830_; lean_object* v_moreLinkArgs_831_; 
v_config_829_ = lean_ctor_get(v_self_828_, 6);
v_toLeanConfig_830_ = lean_ctor_get(v_config_829_, 1);
v_moreLinkArgs_831_ = lean_ctor_get(v_toLeanConfig_830_, 8);
lean_inc_ref(v_moreLinkArgs_831_);
return v_moreLinkArgs_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_Package_moreLinkArgs(v_self_832_);
lean_dec_ref(v_self_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_834_){
_start:
{
lean_object* v_config_835_; lean_object* v_toLeanConfig_836_; lean_object* v_weakLinkArgs_837_; 
v_config_835_ = lean_ctor_get(v_self_834_, 6);
v_toLeanConfig_836_ = lean_ctor_get(v_config_835_, 1);
v_weakLinkArgs_837_ = lean_ctor_get(v_toLeanConfig_836_, 9);
lean_inc_ref(v_weakLinkArgs_837_);
return v_weakLinkArgs_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_Package_weakLinkArgs(v_self_838_);
lean_dec_ref(v_self_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_840_){
_start:
{
lean_object* v_config_841_; lean_object* v_dir_842_; lean_object* v_srcDir_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_config_841_ = lean_ctor_get(v_self_840_, 6);
lean_inc_ref(v_config_841_);
v_dir_842_ = lean_ctor_get(v_self_840_, 4);
lean_inc_ref(v_dir_842_);
lean_dec_ref(v_self_840_);
v_srcDir_843_ = lean_ctor_get(v_config_841_, 4);
lean_inc_ref(v_srcDir_843_);
lean_dec_ref(v_config_841_);
v___x_844_ = l_System_FilePath_normalize(v_srcDir_843_);
v___x_845_ = l_Lake_joinRelative(v_dir_842_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_846_){
_start:
{
lean_object* v_config_847_; lean_object* v_dir_848_; lean_object* v_srcDir_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_config_847_ = lean_ctor_get(v_self_846_, 6);
lean_inc_ref(v_config_847_);
v_dir_848_ = lean_ctor_get(v_self_846_, 4);
lean_inc_ref(v_dir_848_);
lean_dec_ref(v_self_846_);
v_srcDir_849_ = lean_ctor_get(v_config_847_, 4);
lean_inc_ref(v_srcDir_849_);
lean_dec_ref(v_config_847_);
v___x_850_ = l_System_FilePath_normalize(v_srcDir_849_);
v___x_851_ = l_Lake_joinRelative(v_dir_848_, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_852_){
_start:
{
lean_object* v_config_853_; lean_object* v_dir_854_; lean_object* v_buildDir_855_; lean_object* v_leanLibDir_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_config_853_ = lean_ctor_get(v_self_852_, 6);
lean_inc_ref(v_config_853_);
v_dir_854_ = lean_ctor_get(v_self_852_, 4);
lean_inc_ref(v_dir_854_);
lean_dec_ref(v_self_852_);
v_buildDir_855_ = lean_ctor_get(v_config_853_, 5);
lean_inc_ref(v_buildDir_855_);
v_leanLibDir_856_ = lean_ctor_get(v_config_853_, 6);
lean_inc_ref(v_leanLibDir_856_);
lean_dec_ref(v_config_853_);
v___x_857_ = l_System_FilePath_normalize(v_buildDir_855_);
v___x_858_ = l_Lake_joinRelative(v_dir_854_, v___x_857_);
v___x_859_ = l_System_FilePath_normalize(v_leanLibDir_856_);
v___x_860_ = l_Lake_joinRelative(v___x_858_, v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_861_){
_start:
{
lean_object* v_config_862_; lean_object* v_dir_863_; lean_object* v_buildDir_864_; lean_object* v_nativeLibDir_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_config_862_ = lean_ctor_get(v_self_861_, 6);
lean_inc_ref(v_config_862_);
v_dir_863_ = lean_ctor_get(v_self_861_, 4);
lean_inc_ref(v_dir_863_);
lean_dec_ref(v_self_861_);
v_buildDir_864_ = lean_ctor_get(v_config_862_, 5);
lean_inc_ref(v_buildDir_864_);
v_nativeLibDir_865_ = lean_ctor_get(v_config_862_, 7);
lean_inc_ref(v_nativeLibDir_865_);
lean_dec_ref(v_config_862_);
v___x_866_ = l_System_FilePath_normalize(v_buildDir_864_);
v___x_867_ = l_Lake_joinRelative(v_dir_863_, v___x_866_);
v___x_868_ = l_System_FilePath_normalize(v_nativeLibDir_865_);
v___x_869_ = l_Lake_joinRelative(v___x_867_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_870_){
_start:
{
lean_object* v_config_871_; lean_object* v_dir_872_; lean_object* v_buildDir_873_; lean_object* v_nativeLibDir_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_config_871_ = lean_ctor_get(v_self_870_, 6);
lean_inc_ref(v_config_871_);
v_dir_872_ = lean_ctor_get(v_self_870_, 4);
lean_inc_ref(v_dir_872_);
lean_dec_ref(v_self_870_);
v_buildDir_873_ = lean_ctor_get(v_config_871_, 5);
lean_inc_ref(v_buildDir_873_);
v_nativeLibDir_874_ = lean_ctor_get(v_config_871_, 7);
lean_inc_ref(v_nativeLibDir_874_);
lean_dec_ref(v_config_871_);
v___x_875_ = l_System_FilePath_normalize(v_buildDir_873_);
v___x_876_ = l_Lake_joinRelative(v_dir_872_, v___x_875_);
v___x_877_ = l_System_FilePath_normalize(v_nativeLibDir_874_);
v___x_878_ = l_Lake_joinRelative(v___x_876_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_879_){
_start:
{
lean_object* v_config_880_; lean_object* v_dir_881_; lean_object* v_buildDir_882_; lean_object* v_binDir_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_config_880_ = lean_ctor_get(v_self_879_, 6);
lean_inc_ref(v_config_880_);
v_dir_881_ = lean_ctor_get(v_self_879_, 4);
lean_inc_ref(v_dir_881_);
lean_dec_ref(v_self_879_);
v_buildDir_882_ = lean_ctor_get(v_config_880_, 5);
lean_inc_ref(v_buildDir_882_);
v_binDir_883_ = lean_ctor_get(v_config_880_, 8);
lean_inc_ref(v_binDir_883_);
lean_dec_ref(v_config_880_);
v___x_884_ = l_System_FilePath_normalize(v_buildDir_882_);
v___x_885_ = l_Lake_joinRelative(v_dir_881_, v___x_884_);
v___x_886_ = l_System_FilePath_normalize(v_binDir_883_);
v___x_887_ = l_Lake_joinRelative(v___x_885_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_888_){
_start:
{
lean_object* v_config_889_; lean_object* v_dir_890_; lean_object* v_buildDir_891_; lean_object* v_irDir_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_config_889_ = lean_ctor_get(v_self_888_, 6);
lean_inc_ref(v_config_889_);
v_dir_890_ = lean_ctor_get(v_self_888_, 4);
lean_inc_ref(v_dir_890_);
lean_dec_ref(v_self_888_);
v_buildDir_891_ = lean_ctor_get(v_config_889_, 5);
lean_inc_ref(v_buildDir_891_);
v_irDir_892_ = lean_ctor_get(v_config_889_, 9);
lean_inc_ref(v_irDir_892_);
lean_dec_ref(v_config_889_);
v___x_893_ = l_System_FilePath_normalize(v_buildDir_891_);
v___x_894_ = l_Lake_joinRelative(v_dir_890_, v___x_893_);
v___x_895_ = l_System_FilePath_normalize(v_irDir_892_);
v___x_896_ = l_Lake_joinRelative(v___x_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_897_){
_start:
{
lean_object* v_config_898_; uint8_t v_libPrefixOnWindows_899_; 
v_config_898_ = lean_ctor_get(v_self_897_, 6);
v_libPrefixOnWindows_899_ = lean_ctor_get_uint8(v_config_898_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lake_Package_libPrefixOnWindows(v_self_900_);
lean_dec_ref(v_self_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_903_){
_start:
{
lean_object* v_config_904_; lean_object* v_enableArtifactCache_x3f_905_; 
v_config_904_ = lean_ctor_get(v_self_903_, 6);
v_enableArtifactCache_x3f_905_ = lean_ctor_get(v_config_904_, 24);
lean_inc(v_enableArtifactCache_x3f_905_);
return v_enableArtifactCache_x3f_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lake_Package_enableArtifactCache_x3f(v_self_906_);
lean_dec_ref(v_self_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_908_){
_start:
{
lean_object* v_config_909_; lean_object* v_restoreAllArtifacts_x3f_910_; 
v_config_909_ = lean_ctor_get(v_self_908_, 6);
v_restoreAllArtifacts_x3f_910_ = lean_ctor_get(v_config_909_, 25);
lean_inc(v_restoreAllArtifacts_x3f_910_);
return v_restoreAllArtifacts_x3f_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_911_);
lean_dec_ref(v_self_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_913_){
_start:
{
lean_object* v_baseName_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
v_baseName_914_ = lean_ctor_get(v_self_913_, 1);
lean_inc(v_baseName_914_);
lean_dec_ref(v_self_913_);
v___x_915_ = 0;
v___x_916_ = l_Lean_Name_toString(v_baseName_914_, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_918_){
_start:
{
lean_object* v_origName_919_; lean_object* v_scope_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_origName_919_ = lean_ctor_get(v_self_918_, 3);
lean_inc(v_origName_919_);
v_scope_920_ = lean_ctor_get(v_self_918_, 10);
lean_inc_ref(v_scope_920_);
lean_dec_ref(v_self_918_);
v___x_921_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_922_ = lean_string_append(v_scope_920_, v___x_921_);
v___x_923_ = 0;
v___x_924_ = l_Lean_Name_toString(v_origName_919_, v___x_923_);
v___x_925_ = lean_string_append(v___x_922_, v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lake_CacheServiceScope_ofString(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_927_){
_start:
{
lean_object* v_scope_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_scope_928_ = lean_ctor_get(v_self_927_, 10);
v___x_929_ = lean_string_utf8_byte_size(v_scope_928_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_nat_dec_eq(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_927_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v_self_927_);
v___x_934_ = lean_box(0);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_935_, lean_object* v_k_936_){
_start:
{
if (lean_obj_tag(v_t_935_) == 0)
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v_l_939_; lean_object* v_r_940_; uint8_t v___x_941_; 
v_k_937_ = lean_ctor_get(v_t_935_, 1);
v_v_938_ = lean_ctor_get(v_t_935_, 2);
v_l_939_ = lean_ctor_get(v_t_935_, 3);
v_r_940_ = lean_ctor_get(v_t_935_, 4);
v___x_941_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_936_, v_k_937_);
switch(v___x_941_)
{
case 0:
{
v_t_935_ = v_l_939_;
goto _start;
}
case 1:
{
lean_object* v___x_943_; 
lean_inc(v_v_938_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_v_938_);
return v___x_943_;
}
default: 
{
v_t_935_ = v_r_940_;
goto _start;
}
}
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_box(0);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_946_, lean_object* v_k_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_946_, v_k_947_);
lean_dec(v_k_947_);
lean_dec(v_t_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_949_, lean_object* v_self_950_){
_start:
{
lean_object* v_targetDeclMap_951_; lean_object* v___x_952_; 
v_targetDeclMap_951_ = lean_ctor_get(v_self_950_, 16);
v___x_952_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_951_, v_name_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_953_, lean_object* v_self_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lake_Package_findTargetDecl_x3f(v_name_953_, v_self_954_);
lean_dec_ref(v_self_954_);
lean_dec(v_name_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_956_, lean_object* v_inst_957_, lean_object* v_t_958_, lean_object* v_k_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_958_, v_k_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_961_, lean_object* v_inst_962_, lean_object* v_t_963_, lean_object* v_k_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_961_, v_inst_962_, v_t_963_, v_k_964_);
lean_dec(v_k_964_);
lean_dec(v_t_963_);
return v_res_965_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_969_, lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_971_, v_stop_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v_kind_975_; lean_object* v_config_976_; uint8_t v___x_977_; uint8_t v___y_979_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_974_ = lean_array_uget_borrowed(v_as_970_, v_i_971_);
v_kind_975_ = lean_ctor_get(v___x_974_, 2);
v_config_976_ = lean_ctor_get(v___x_974_, 3);
v___x_977_ = 1;
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_984_ = lean_name_eq(v_kind_975_, v___x_983_);
if (v___x_984_ == 0)
{
v___y_979_ = v___x_973_;
goto v___jp_978_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_969_, v_config_976_);
v___y_979_ = v___x_985_;
goto v___jp_978_;
}
v___jp_978_:
{
if (v___y_979_ == 0)
{
size_t v___x_980_; size_t v___x_981_; 
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_971_, v___x_980_);
v_i_971_ = v___x_981_;
goto _start;
}
else
{
return v___x_977_;
}
}
}
else
{
uint8_t v___x_986_; 
v___x_986_ = 0;
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_987_, lean_object* v_as_988_, lean_object* v_i_989_, lean_object* v_stop_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; uint8_t v_res_993_; lean_object* v_r_994_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_989_);
lean_dec(v_i_989_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_990_);
lean_dec(v_stop_990_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_987_, v_as_988_, v_i_boxed_991_, v_stop_boxed_992_);
lean_dec_ref(v_as_988_);
lean_dec(v_mod_987_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_995_, lean_object* v_self_996_){
_start:
{
lean_object* v_targetDecls_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_targetDecls_997_ = lean_ctor_get(v_self_996_, 15);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_array_get_size(v_targetDecls_997_);
v___x_1000_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
return v___x_1000_;
}
else
{
if (v___x_1000_ == 0)
{
return v___x_1000_;
}
else
{
size_t v___x_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = lean_usize_of_nat(v___x_999_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_995_, v_targetDecls_997_, v___x_1001_, v___x_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1004_, lean_object* v_self_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lake_Package_isLocalModule(v_mod_1004_, v_self_1005_);
lean_dec_ref(v_self_1005_);
lean_dec(v_mod_1004_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1008_, lean_object* v_as_1009_, size_t v_i_1010_, size_t v_stop_1011_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_eq(v_i_1010_, v_stop_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v_kind_1014_; lean_object* v_config_1015_; uint8_t v___x_1016_; uint8_t v___y_1018_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1013_ = lean_array_uget_borrowed(v_as_1009_, v_i_1010_);
v_kind_1014_ = lean_ctor_get(v___x_1013_, 2);
v_config_1015_ = lean_ctor_get(v___x_1013_, 3);
v___x_1016_ = 1;
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1030_ = lean_name_eq(v_kind_1014_, v___x_1029_);
if (v___x_1030_ == 0)
{
goto v___jp_1022_;
}
else
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1008_, v_config_1015_);
if (v___x_1031_ == 0)
{
goto v___jp_1022_;
}
else
{
v___y_1018_ = v___x_1031_;
goto v___jp_1017_;
}
}
v___jp_1017_:
{
if (v___y_1018_ == 0)
{
size_t v___x_1019_; size_t v___x_1020_; 
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_add(v_i_1010_, v___x_1019_);
v_i_1010_ = v___x_1020_;
goto _start;
}
else
{
return v___x_1016_;
}
}
v___jp_1022_:
{
lean_object* v_kind_1023_; lean_object* v_config_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_kind_1023_ = lean_ctor_get(v___x_1013_, 2);
v_config_1024_ = lean_ctor_get(v___x_1013_, 3);
v___x_1025_ = l_Lake_LeanExe_keyword;
v___x_1026_ = lean_name_eq(v_kind_1023_, v___x_1025_);
if (v___x_1026_ == 0)
{
v___y_1018_ = v___x_1012_;
goto v___jp_1017_;
}
else
{
lean_object* v_root_1027_; uint8_t v___x_1028_; 
v_root_1027_ = lean_ctor_get(v_config_1024_, 2);
v___x_1028_ = lean_name_eq(v_root_1027_, v_mod_1008_);
v___y_1018_ = v___x_1028_;
goto v___jp_1017_;
}
}
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = 0;
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1033_, lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_stop_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1036_);
lean_dec(v_stop_1036_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1033_, v_as_1034_, v_i_boxed_1037_, v_stop_boxed_1038_);
lean_dec_ref(v_as_1034_);
lean_dec(v_mod_1033_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1041_, lean_object* v_self_1042_){
_start:
{
lean_object* v_targetDecls_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_targetDecls_1043_ = lean_ctor_get(v_self_1042_, 15);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_array_get_size(v_targetDecls_1043_);
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
return v___x_1046_;
}
else
{
if (v___x_1046_ == 0)
{
return v___x_1046_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_of_nat(v___x_1045_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1041_, v_targetDecls_1043_, v___x_1047_, v___x_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1050_, lean_object* v_self_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_Lake_Package_isBuildableModule(v_mod_1050_, v_self_1051_);
lean_dec_ref(v_self_1051_);
lean_dec(v_mod_1050_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1054_){
_start:
{
lean_object* v_config_1056_; lean_object* v_dir_1057_; lean_object* v_buildDir_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_config_1056_ = lean_ctor_get(v_self_1054_, 6);
lean_inc_ref(v_config_1056_);
v_dir_1057_ = lean_ctor_get(v_self_1054_, 4);
lean_inc_ref(v_dir_1057_);
lean_dec_ref(v_self_1054_);
v_buildDir_1058_ = lean_ctor_get(v_config_1056_, 5);
lean_inc_ref(v_buildDir_1058_);
lean_dec_ref(v_config_1056_);
v___x_1059_ = l_System_FilePath_normalize(v_buildDir_1058_);
v___x_1060_ = l_Lake_joinRelative(v_dir_1057_, v___x_1059_);
v___x_1061_ = l_Lake_removeDirAllIfExists(v___x_1060_);
lean_dec_ref(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lake_Package_clean(v_self_1062_);
return v_res_1064_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
