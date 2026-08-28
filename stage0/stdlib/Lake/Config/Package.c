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
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_Platform_target;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_Package_isPlatformIndependent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_isPlatformIndependent___closed__0 = (const lean_object*)&l_Lake_Package_isPlatformIndependent___closed__0_value;
static const lean_closure_object l_Lake_Package_isPlatformIndependent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_Package_isPlatformIndependent___closed__0_value)} };
static const lean_object* l_Lake_Package_isPlatformIndependent___closed__1 = (const lean_object*)&l_Lake_Package_isPlatformIndependent___closed__1_value;
static const lean_ctor_object l_Lake_Package_isPlatformIndependent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Package_isPlatformIndependent___closed__2 = (const lean_object*)&l_Lake_Package_isPlatformIndependent___closed__2_value;
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
static const lean_string_object l_Lake_Package_bootstrapIncludeDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lake_Package_bootstrapIncludeDir___closed__0 = (const lean_object*)&l_Lake_Package_bootstrapIncludeDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object*);
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
lean_inc_ref(v___y_361_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_360_);
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
lean_ctor_set(v___x_365_, 17, v___y_360_);
lean_ctor_set(v___x_365_, 18, v___y_359_);
lean_ctor_set(v___x_365_, 19, v___y_358_);
lean_ctor_set(v___x_365_, 20, v___y_361_);
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
v___y_359_ = v___x_369_;
v___y_360_ = v___x_355_;
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
v___y_359_ = v___x_369_;
v___y_360_ = v___x_355_;
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
v_bootstrap_515_ = lean_ctor_get_uint8(v_config_514_, sizeof(void*)*28);
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
v_bootstrap_521_ = lean_ctor_get_uint8(v_config_520_, sizeof(void*)*28);
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
v_reservoir_553_ = lean_ctor_get_uint8(v_config_552_, sizeof(void*)*28 + 3);
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
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_671_){
_start:
{
lean_object* v_config_672_; lean_object* v_toLeanConfig_673_; lean_object* v_platformIndependent_674_; lean_object* v___f_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_config_672_ = lean_ctor_get(v_self_671_, 6);
lean_inc_ref(v_config_672_);
lean_dec_ref(v_self_671_);
v_toLeanConfig_673_ = lean_ctor_get(v_config_672_, 1);
lean_inc_ref(v_toLeanConfig_673_);
lean_dec_ref(v_config_672_);
v_platformIndependent_674_ = lean_ctor_get(v_toLeanConfig_673_, 10);
lean_inc(v_platformIndependent_674_);
lean_dec_ref(v_toLeanConfig_673_);
v___f_675_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_676_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_677_ = l_Option_instBEq_beq___redArg(v___f_675_, v_platformIndependent_674_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Lake_Package_isPlatformIndependent(v_self_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_681_){
_start:
{
lean_object* v_config_682_; uint8_t v_fixedToolchain_683_; 
v_config_682_ = lean_ctor_get(v_self_681_, 6);
v_fixedToolchain_683_ = lean_ctor_get_uint8(v_config_682_, sizeof(void*)*28 + 6);
return v_fixedToolchain_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lake_Package_fixedToolchain(v_self_684_);
lean_dec_ref(v_self_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_687_){
_start:
{
lean_object* v_config_688_; lean_object* v_releaseRepo_689_; 
v_config_688_ = lean_ctor_get(v_self_687_, 6);
v_releaseRepo_689_ = lean_ctor_get(v_config_688_, 10);
lean_inc(v_releaseRepo_689_);
return v_releaseRepo_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lake_Package_releaseRepo_x3f(v_self_690_);
lean_dec_ref(v_self_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_692_){
_start:
{
lean_object* v_remoteUrl_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_remoteUrl_693_ = lean_ctor_get(v_self_692_, 11);
v___x_694_ = lean_string_utf8_byte_size(v_remoteUrl_693_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_nat_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_inc_ref(v_remoteUrl_693_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_remoteUrl_693_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_Package_remoteUrl_x3f(v_self_699_);
lean_dec_ref(v_self_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_701_){
_start:
{
lean_object* v_dir_702_; lean_object* v_buildArchive_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_dir_702_ = lean_ctor_get(v_self_701_, 4);
lean_inc_ref(v_dir_702_);
v_buildArchive_703_ = lean_ctor_get(v_self_701_, 21);
lean_inc_ref(v_buildArchive_703_);
lean_dec_ref(v_self_701_);
v___x_704_ = l_Lake_defaultLakeDir;
v___x_705_ = l_Lake_joinRelative(v_dir_702_, v___x_704_);
v___x_706_ = l_Lake_joinRelative(v___x_705_, v_buildArchive_703_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_708_){
_start:
{
lean_object* v_dir_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_dir_709_ = lean_ctor_get(v_self_708_, 4);
lean_inc_ref(v_dir_709_);
lean_dec_ref(v_self_708_);
v___x_710_ = l_Lake_defaultLakeDir;
v___x_711_ = l_Lake_joinRelative(v_dir_709_, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_713_ = l_Lake_joinRelative(v___x_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_714_){
_start:
{
lean_object* v_config_715_; uint8_t v_preferReleaseBuild_716_; 
v_config_715_ = lean_ctor_get(v_self_714_, 6);
v_preferReleaseBuild_716_ = lean_ctor_get_uint8(v_config_715_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lake_Package_preferReleaseBuild(v_self_717_);
lean_dec_ref(v_self_717_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_720_){
_start:
{
lean_object* v_config_721_; uint8_t v_precompileModules_722_; 
v_config_721_ = lean_ctor_get(v_self_720_, 6);
v_precompileModules_722_ = lean_ctor_get_uint8(v_config_721_, sizeof(void*)*28 + 1);
return v_precompileModules_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_Lake_Package_precompileModules(v_self_723_);
lean_dec_ref(v_self_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_726_){
_start:
{
lean_object* v_config_727_; lean_object* v_moreGlobalServerArgs_728_; 
v_config_727_ = lean_ctor_get(v_self_726_, 6);
v_moreGlobalServerArgs_728_ = lean_ctor_get(v_config_727_, 3);
lean_inc_ref(v_moreGlobalServerArgs_728_);
return v_moreGlobalServerArgs_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lake_Package_moreGlobalServerArgs(v_self_729_);
lean_dec_ref(v_self_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_731_){
_start:
{
lean_object* v_config_732_; lean_object* v_toLeanConfig_733_; lean_object* v_leanOptions_734_; lean_object* v_moreServerOptions_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_config_732_ = lean_ctor_get(v_self_731_, 6);
v_toLeanConfig_733_ = lean_ctor_get(v_config_732_, 1);
v_leanOptions_734_ = lean_ctor_get(v_toLeanConfig_733_, 0);
v_moreServerOptions_735_ = lean_ctor_get(v_toLeanConfig_733_, 4);
v___x_736_ = l_Lean_LeanOptions_ofArray(v_leanOptions_734_);
v___x_737_ = l_Lean_LeanOptions_appendArray(v___x_736_, v_moreServerOptions_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lake_Package_moreServerOptions(v_self_738_);
lean_dec_ref(v_self_738_);
return v_res_739_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_740_){
_start:
{
lean_object* v_config_741_; lean_object* v_toLeanConfig_742_; uint8_t v_buildType_743_; 
v_config_741_ = lean_ctor_get(v_self_740_, 6);
v_toLeanConfig_742_ = lean_ctor_get(v_config_741_, 1);
v_buildType_743_ = lean_ctor_get_uint8(v_toLeanConfig_742_, sizeof(void*)*13);
return v_buildType_743_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lake_Package_buildType(v_self_744_);
lean_dec_ref(v_self_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_747_){
_start:
{
lean_object* v_config_748_; lean_object* v_toLeanConfig_749_; uint8_t v_backend_750_; 
v_config_748_ = lean_ctor_get(v_self_747_, 6);
v_toLeanConfig_749_ = lean_ctor_get(v_config_748_, 1);
v_backend_750_ = lean_ctor_get_uint8(v_toLeanConfig_749_, sizeof(void*)*13 + 1);
return v_backend_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lake_Package_backend(v_self_751_);
lean_dec_ref(v_self_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_754_){
_start:
{
lean_object* v_config_755_; uint8_t v_allowImportAll_756_; 
v_config_755_ = lean_ctor_get(v_self_754_, 6);
v_allowImportAll_756_ = lean_ctor_get_uint8(v_config_755_, sizeof(void*)*28 + 5);
return v_allowImportAll_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lake_Package_allowImportAll(v_self_757_);
lean_dec_ref(v_self_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_760_){
_start:
{
lean_object* v_config_761_; lean_object* v_toLeanConfig_762_; uint8_t v_requiresModuleSystem_763_; 
v_config_761_ = lean_ctor_get(v_self_760_, 6);
v_toLeanConfig_762_ = lean_ctor_get(v_config_761_, 1);
v_requiresModuleSystem_763_ = lean_ctor_get_uint8(v_toLeanConfig_762_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Lake_Package_requiresModuleSystem(v_self_764_);
lean_dec_ref(v_self_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_767_){
_start:
{
lean_object* v_config_768_; lean_object* v_toLeanConfig_769_; uint8_t v_allowNonModules_770_; 
v_config_768_ = lean_ctor_get(v_self_767_, 6);
v_toLeanConfig_769_ = lean_ctor_get(v_config_768_, 1);
v_allowNonModules_770_ = lean_ctor_get_uint8(v_toLeanConfig_769_, sizeof(void*)*13 + 3);
return v_allowNonModules_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Lake_Package_allowNonModules(v_self_771_);
lean_dec_ref(v_self_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_774_){
_start:
{
lean_object* v_config_775_; lean_object* v_toLeanConfig_776_; lean_object* v_dynlibs_777_; 
v_config_775_ = lean_ctor_get(v_self_774_, 6);
v_toLeanConfig_776_ = lean_ctor_get(v_config_775_, 1);
v_dynlibs_777_ = lean_ctor_get(v_toLeanConfig_776_, 11);
lean_inc_ref(v_dynlibs_777_);
return v_dynlibs_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_Package_dynlibs(v_self_778_);
lean_dec_ref(v_self_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_780_){
_start:
{
lean_object* v_config_781_; lean_object* v_toLeanConfig_782_; lean_object* v_plugins_783_; 
v_config_781_ = lean_ctor_get(v_self_780_, 6);
v_toLeanConfig_782_ = lean_ctor_get(v_config_781_, 1);
v_plugins_783_ = lean_ctor_get(v_toLeanConfig_782_, 12);
lean_inc_ref(v_plugins_783_);
return v_plugins_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_Package_plugins(v_self_784_);
lean_dec_ref(v_self_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_786_){
_start:
{
lean_object* v_config_787_; lean_object* v_toLeanConfig_788_; lean_object* v_leanOptions_789_; lean_object* v___x_790_; 
v_config_787_ = lean_ctor_get(v_self_786_, 6);
v_toLeanConfig_788_ = lean_ctor_get(v_config_787_, 1);
v_leanOptions_789_ = lean_ctor_get(v_toLeanConfig_788_, 0);
v___x_790_ = l_Lean_LeanOptions_ofArray(v_leanOptions_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lake_Package_leanOptions(v_self_791_);
lean_dec_ref(v_self_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_793_){
_start:
{
lean_object* v_config_794_; lean_object* v_toLeanConfig_795_; lean_object* v_moreLeanArgs_796_; 
v_config_794_ = lean_ctor_get(v_self_793_, 6);
v_toLeanConfig_795_ = lean_ctor_get(v_config_794_, 1);
v_moreLeanArgs_796_ = lean_ctor_get(v_toLeanConfig_795_, 1);
lean_inc_ref(v_moreLeanArgs_796_);
return v_moreLeanArgs_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_Package_moreLeanArgs(v_self_797_);
lean_dec_ref(v_self_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_799_){
_start:
{
lean_object* v_config_800_; lean_object* v_toLeanConfig_801_; lean_object* v_weakLeanArgs_802_; 
v_config_800_ = lean_ctor_get(v_self_799_, 6);
v_toLeanConfig_801_ = lean_ctor_get(v_config_800_, 1);
v_weakLeanArgs_802_ = lean_ctor_get(v_toLeanConfig_801_, 2);
lean_inc_ref(v_weakLeanArgs_802_);
return v_weakLeanArgs_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lake_Package_weakLeanArgs(v_self_803_);
lean_dec_ref(v_self_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_805_){
_start:
{
lean_object* v_config_806_; lean_object* v_toLeanConfig_807_; lean_object* v_moreLeancArgs_808_; 
v_config_806_ = lean_ctor_get(v_self_805_, 6);
v_toLeanConfig_807_ = lean_ctor_get(v_config_806_, 1);
v_moreLeancArgs_808_ = lean_ctor_get(v_toLeanConfig_807_, 3);
lean_inc_ref(v_moreLeancArgs_808_);
return v_moreLeancArgs_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lake_Package_moreLeancArgs(v_self_809_);
lean_dec_ref(v_self_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_811_){
_start:
{
lean_object* v_config_812_; lean_object* v_toLeanConfig_813_; lean_object* v_weakLeancArgs_814_; 
v_config_812_ = lean_ctor_get(v_self_811_, 6);
v_toLeanConfig_813_ = lean_ctor_get(v_config_812_, 1);
v_weakLeancArgs_814_ = lean_ctor_get(v_toLeanConfig_813_, 5);
lean_inc_ref(v_weakLeancArgs_814_);
return v_weakLeancArgs_814_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lake_Package_weakLeancArgs(v_self_815_);
lean_dec_ref(v_self_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_817_){
_start:
{
lean_object* v_config_818_; lean_object* v_toLeanConfig_819_; lean_object* v_moreLinkObjs_820_; 
v_config_818_ = lean_ctor_get(v_self_817_, 6);
v_toLeanConfig_819_ = lean_ctor_get(v_config_818_, 1);
v_moreLinkObjs_820_ = lean_ctor_get(v_toLeanConfig_819_, 6);
lean_inc_ref(v_moreLinkObjs_820_);
return v_moreLinkObjs_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lake_Package_moreLinkObjs(v_self_821_);
lean_dec_ref(v_self_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_823_){
_start:
{
lean_object* v_config_824_; lean_object* v_toLeanConfig_825_; lean_object* v_moreLinkLibs_826_; 
v_config_824_ = lean_ctor_get(v_self_823_, 6);
v_toLeanConfig_825_ = lean_ctor_get(v_config_824_, 1);
v_moreLinkLibs_826_ = lean_ctor_get(v_toLeanConfig_825_, 7);
lean_inc_ref(v_moreLinkLibs_826_);
return v_moreLinkLibs_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lake_Package_moreLinkLibs(v_self_827_);
lean_dec_ref(v_self_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_829_){
_start:
{
lean_object* v_config_830_; lean_object* v_toLeanConfig_831_; lean_object* v_moreLinkArgs_832_; 
v_config_830_ = lean_ctor_get(v_self_829_, 6);
v_toLeanConfig_831_ = lean_ctor_get(v_config_830_, 1);
v_moreLinkArgs_832_ = lean_ctor_get(v_toLeanConfig_831_, 8);
lean_inc_ref(v_moreLinkArgs_832_);
return v_moreLinkArgs_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lake_Package_moreLinkArgs(v_self_833_);
lean_dec_ref(v_self_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_835_){
_start:
{
lean_object* v_config_836_; lean_object* v_toLeanConfig_837_; lean_object* v_weakLinkArgs_838_; 
v_config_836_ = lean_ctor_get(v_self_835_, 6);
v_toLeanConfig_837_ = lean_ctor_get(v_config_836_, 1);
v_weakLinkArgs_838_ = lean_ctor_get(v_toLeanConfig_837_, 9);
lean_inc_ref(v_weakLinkArgs_838_);
return v_weakLinkArgs_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_Package_weakLinkArgs(v_self_839_);
lean_dec_ref(v_self_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_841_){
_start:
{
lean_object* v_config_842_; lean_object* v_dir_843_; lean_object* v_srcDir_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_config_842_ = lean_ctor_get(v_self_841_, 6);
lean_inc_ref(v_config_842_);
v_dir_843_ = lean_ctor_get(v_self_841_, 4);
lean_inc_ref(v_dir_843_);
lean_dec_ref(v_self_841_);
v_srcDir_844_ = lean_ctor_get(v_config_842_, 4);
lean_inc_ref(v_srcDir_844_);
lean_dec_ref(v_config_842_);
v___x_845_ = l_System_FilePath_normalize(v_srcDir_844_);
v___x_846_ = l_Lake_joinRelative(v_dir_843_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_847_){
_start:
{
lean_object* v_config_848_; lean_object* v_dir_849_; lean_object* v_srcDir_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_config_848_ = lean_ctor_get(v_self_847_, 6);
lean_inc_ref(v_config_848_);
v_dir_849_ = lean_ctor_get(v_self_847_, 4);
lean_inc_ref(v_dir_849_);
lean_dec_ref(v_self_847_);
v_srcDir_850_ = lean_ctor_get(v_config_848_, 4);
lean_inc_ref(v_srcDir_850_);
lean_dec_ref(v_config_848_);
v___x_851_ = l_System_FilePath_normalize(v_srcDir_850_);
v___x_852_ = l_Lake_joinRelative(v_dir_849_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_853_){
_start:
{
lean_object* v_config_854_; lean_object* v_dir_855_; lean_object* v_buildDir_856_; lean_object* v_leanLibDir_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_config_854_ = lean_ctor_get(v_self_853_, 6);
lean_inc_ref(v_config_854_);
v_dir_855_ = lean_ctor_get(v_self_853_, 4);
lean_inc_ref(v_dir_855_);
lean_dec_ref(v_self_853_);
v_buildDir_856_ = lean_ctor_get(v_config_854_, 5);
lean_inc_ref(v_buildDir_856_);
v_leanLibDir_857_ = lean_ctor_get(v_config_854_, 6);
lean_inc_ref(v_leanLibDir_857_);
lean_dec_ref(v_config_854_);
v___x_858_ = l_System_FilePath_normalize(v_buildDir_856_);
v___x_859_ = l_Lake_joinRelative(v_dir_855_, v___x_858_);
v___x_860_ = l_System_FilePath_normalize(v_leanLibDir_857_);
v___x_861_ = l_Lake_joinRelative(v___x_859_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object* v_self_863_){
_start:
{
lean_object* v_config_864_; lean_object* v_dir_865_; lean_object* v_buildDir_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_config_864_ = lean_ctor_get(v_self_863_, 6);
lean_inc_ref(v_config_864_);
v_dir_865_ = lean_ctor_get(v_self_863_, 4);
lean_inc_ref(v_dir_865_);
lean_dec_ref(v_self_863_);
v_buildDir_866_ = lean_ctor_get(v_config_864_, 5);
lean_inc_ref(v_buildDir_866_);
lean_dec_ref(v_config_864_);
v___x_867_ = l_System_FilePath_normalize(v_buildDir_866_);
v___x_868_ = l_Lake_joinRelative(v_dir_865_, v___x_867_);
v___x_869_ = ((lean_object*)(l_Lake_Package_bootstrapIncludeDir___closed__0));
v___x_870_ = l_Lake_joinRelative(v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_871_){
_start:
{
lean_object* v_config_872_; lean_object* v_dir_873_; lean_object* v_buildDir_874_; lean_object* v_nativeLibDir_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_config_872_ = lean_ctor_get(v_self_871_, 6);
lean_inc_ref(v_config_872_);
v_dir_873_ = lean_ctor_get(v_self_871_, 4);
lean_inc_ref(v_dir_873_);
lean_dec_ref(v_self_871_);
v_buildDir_874_ = lean_ctor_get(v_config_872_, 5);
lean_inc_ref(v_buildDir_874_);
v_nativeLibDir_875_ = lean_ctor_get(v_config_872_, 7);
lean_inc_ref(v_nativeLibDir_875_);
lean_dec_ref(v_config_872_);
v___x_876_ = l_System_FilePath_normalize(v_buildDir_874_);
v___x_877_ = l_Lake_joinRelative(v_dir_873_, v___x_876_);
v___x_878_ = l_System_FilePath_normalize(v_nativeLibDir_875_);
v___x_879_ = l_Lake_joinRelative(v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_880_){
_start:
{
lean_object* v_config_881_; lean_object* v_dir_882_; lean_object* v_buildDir_883_; lean_object* v_nativeLibDir_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_config_881_ = lean_ctor_get(v_self_880_, 6);
lean_inc_ref(v_config_881_);
v_dir_882_ = lean_ctor_get(v_self_880_, 4);
lean_inc_ref(v_dir_882_);
lean_dec_ref(v_self_880_);
v_buildDir_883_ = lean_ctor_get(v_config_881_, 5);
lean_inc_ref(v_buildDir_883_);
v_nativeLibDir_884_ = lean_ctor_get(v_config_881_, 7);
lean_inc_ref(v_nativeLibDir_884_);
lean_dec_ref(v_config_881_);
v___x_885_ = l_System_FilePath_normalize(v_buildDir_883_);
v___x_886_ = l_Lake_joinRelative(v_dir_882_, v___x_885_);
v___x_887_ = l_System_FilePath_normalize(v_nativeLibDir_884_);
v___x_888_ = l_Lake_joinRelative(v___x_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_889_){
_start:
{
lean_object* v_config_890_; lean_object* v_dir_891_; lean_object* v_buildDir_892_; lean_object* v_binDir_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_config_890_ = lean_ctor_get(v_self_889_, 6);
lean_inc_ref(v_config_890_);
v_dir_891_ = lean_ctor_get(v_self_889_, 4);
lean_inc_ref(v_dir_891_);
lean_dec_ref(v_self_889_);
v_buildDir_892_ = lean_ctor_get(v_config_890_, 5);
lean_inc_ref(v_buildDir_892_);
v_binDir_893_ = lean_ctor_get(v_config_890_, 8);
lean_inc_ref(v_binDir_893_);
lean_dec_ref(v_config_890_);
v___x_894_ = l_System_FilePath_normalize(v_buildDir_892_);
v___x_895_ = l_Lake_joinRelative(v_dir_891_, v___x_894_);
v___x_896_ = l_System_FilePath_normalize(v_binDir_893_);
v___x_897_ = l_Lake_joinRelative(v___x_895_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_898_){
_start:
{
lean_object* v_config_899_; lean_object* v_dir_900_; lean_object* v_buildDir_901_; lean_object* v_irDir_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_config_899_ = lean_ctor_get(v_self_898_, 6);
lean_inc_ref(v_config_899_);
v_dir_900_ = lean_ctor_get(v_self_898_, 4);
lean_inc_ref(v_dir_900_);
lean_dec_ref(v_self_898_);
v_buildDir_901_ = lean_ctor_get(v_config_899_, 5);
lean_inc_ref(v_buildDir_901_);
v_irDir_902_ = lean_ctor_get(v_config_899_, 9);
lean_inc_ref(v_irDir_902_);
lean_dec_ref(v_config_899_);
v___x_903_ = l_System_FilePath_normalize(v_buildDir_901_);
v___x_904_ = l_Lake_joinRelative(v_dir_900_, v___x_903_);
v___x_905_ = l_System_FilePath_normalize(v_irDir_902_);
v___x_906_ = l_Lake_joinRelative(v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_907_){
_start:
{
lean_object* v_config_908_; uint8_t v_libPrefixOnWindows_909_; 
v_config_908_ = lean_ctor_get(v_self_907_, 6);
v_libPrefixOnWindows_909_ = lean_ctor_get_uint8(v_config_908_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Lake_Package_libPrefixOnWindows(v_self_910_);
lean_dec_ref(v_self_910_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_913_){
_start:
{
lean_object* v_config_914_; lean_object* v_enableArtifactCache_x3f_915_; 
v_config_914_ = lean_ctor_get(v_self_913_, 6);
v_enableArtifactCache_x3f_915_ = lean_ctor_get(v_config_914_, 24);
lean_inc(v_enableArtifactCache_x3f_915_);
return v_enableArtifactCache_x3f_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lake_Package_enableArtifactCache_x3f(v_self_916_);
lean_dec_ref(v_self_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_918_){
_start:
{
lean_object* v_config_919_; lean_object* v_restoreAllArtifacts_x3f_920_; 
v_config_919_ = lean_ctor_get(v_self_918_, 6);
v_restoreAllArtifacts_x3f_920_ = lean_ctor_get(v_config_919_, 25);
lean_inc(v_restoreAllArtifacts_x3f_920_);
return v_restoreAllArtifacts_x3f_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_921_);
lean_dec_ref(v_self_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_923_){
_start:
{
lean_object* v_baseName_924_; uint8_t v___x_925_; lean_object* v___x_926_; 
v_baseName_924_ = lean_ctor_get(v_self_923_, 1);
lean_inc(v_baseName_924_);
lean_dec_ref(v_self_923_);
v___x_925_ = 0;
v___x_926_ = l_Lean_Name_toString(v_baseName_924_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_928_){
_start:
{
lean_object* v_origName_929_; lean_object* v_scope_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_origName_929_ = lean_ctor_get(v_self_928_, 3);
lean_inc(v_origName_929_);
v_scope_930_ = lean_ctor_get(v_self_928_, 10);
lean_inc_ref(v_scope_930_);
lean_dec_ref(v_self_928_);
v___x_931_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_932_ = lean_string_append(v_scope_930_, v___x_931_);
v___x_933_ = 0;
v___x_934_ = l_Lean_Name_toString(v_origName_929_, v___x_933_);
v___x_935_ = lean_string_append(v___x_932_, v___x_934_);
lean_dec_ref(v___x_934_);
v___x_936_ = l_Lake_CacheServiceScope_ofString(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_937_){
_start:
{
lean_object* v_scope_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_scope_938_ = lean_ctor_get(v_self_937_, 10);
v___x_939_ = lean_string_utf8_byte_size(v_scope_938_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_nat_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_937_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_self_937_);
v___x_944_ = lean_box(0);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_945_, lean_object* v_k_946_){
_start:
{
if (lean_obj_tag(v_t_945_) == 0)
{
lean_object* v_k_947_; lean_object* v_v_948_; lean_object* v_l_949_; lean_object* v_r_950_; uint8_t v___x_951_; 
v_k_947_ = lean_ctor_get(v_t_945_, 1);
v_v_948_ = lean_ctor_get(v_t_945_, 2);
v_l_949_ = lean_ctor_get(v_t_945_, 3);
v_r_950_ = lean_ctor_get(v_t_945_, 4);
v___x_951_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_946_, v_k_947_);
switch(v___x_951_)
{
case 0:
{
v_t_945_ = v_l_949_;
goto _start;
}
case 1:
{
lean_object* v___x_953_; 
lean_inc(v_v_948_);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v_v_948_);
return v___x_953_;
}
default: 
{
v_t_945_ = v_r_950_;
goto _start;
}
}
}
else
{
lean_object* v___x_955_; 
v___x_955_ = lean_box(0);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_956_, lean_object* v_k_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_956_, v_k_957_);
lean_dec(v_k_957_);
lean_dec(v_t_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_959_, lean_object* v_self_960_){
_start:
{
lean_object* v_targetDeclMap_961_; lean_object* v___x_962_; 
v_targetDeclMap_961_ = lean_ctor_get(v_self_960_, 16);
v___x_962_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_961_, v_name_959_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_963_, lean_object* v_self_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lake_Package_findTargetDecl_x3f(v_name_963_, v_self_964_);
lean_dec_ref(v_self_964_);
lean_dec(v_name_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_966_, lean_object* v_inst_967_, lean_object* v_t_968_, lean_object* v_k_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_968_, v_k_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_971_, lean_object* v_inst_972_, lean_object* v_t_973_, lean_object* v_k_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_971_, v_inst_972_, v_t_973_, v_k_974_);
lean_dec(v_k_974_);
lean_dec(v_t_973_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_979_, lean_object* v_as_980_, size_t v_i_981_, size_t v_stop_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_eq(v_i_981_, v_stop_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v_kind_985_; lean_object* v_config_986_; uint8_t v___x_987_; uint8_t v___y_989_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_984_ = lean_array_uget_borrowed(v_as_980_, v_i_981_);
v_kind_985_ = lean_ctor_get(v___x_984_, 2);
v_config_986_ = lean_ctor_get(v___x_984_, 3);
v___x_987_ = 1;
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_994_ = lean_name_eq(v_kind_985_, v___x_993_);
if (v___x_994_ == 0)
{
v___y_989_ = v___x_994_;
goto v___jp_988_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_979_, v_config_986_);
v___y_989_ = v___x_995_;
goto v___jp_988_;
}
v___jp_988_:
{
if (v___y_989_ == 0)
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_981_, v___x_990_);
v_i_981_ = v___x_991_;
goto _start;
}
else
{
return v___x_987_;
}
}
}
else
{
uint8_t v___x_996_; 
v___x_996_ = 0;
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_997_, lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_){
_start:
{
size_t v_i_boxed_1001_; size_t v_stop_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_i_boxed_1001_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1002_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_997_, v_as_998_, v_i_boxed_1001_, v_stop_boxed_1002_);
lean_dec_ref(v_as_998_);
lean_dec(v_mod_997_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_1005_, lean_object* v_self_1006_){
_start:
{
lean_object* v_targetDecls_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_targetDecls_1007_ = lean_ctor_get(v_self_1006_, 15);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_array_get_size(v_targetDecls_1007_);
v___x_1010_ = lean_nat_dec_lt(v___x_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
return v___x_1010_;
}
else
{
if (v___x_1010_ == 0)
{
return v___x_1010_;
}
else
{
size_t v___x_1011_; size_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = lean_usize_of_nat(v___x_1009_);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1005_, v_targetDecls_1007_, v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1014_, lean_object* v_self_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Lake_Package_isLocalModule(v_mod_1014_, v_self_1015_);
lean_dec_ref(v_self_1015_);
lean_dec(v_mod_1014_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1018_, lean_object* v_as_1019_, size_t v_i_1020_, size_t v_stop_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_eq(v_i_1020_, v_stop_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v_kind_1024_; lean_object* v_config_1025_; uint8_t v___x_1026_; uint8_t v___y_1028_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1023_ = lean_array_uget_borrowed(v_as_1019_, v_i_1020_);
v_kind_1024_ = lean_ctor_get(v___x_1023_, 2);
v_config_1025_ = lean_ctor_get(v___x_1023_, 3);
v___x_1026_ = 1;
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1040_ = lean_name_eq(v_kind_1024_, v___x_1039_);
if (v___x_1040_ == 0)
{
goto v___jp_1032_;
}
else
{
uint8_t v___x_1041_; 
v___x_1041_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1018_, v_config_1025_);
if (v___x_1041_ == 0)
{
goto v___jp_1032_;
}
else
{
v___y_1028_ = v___x_1041_;
goto v___jp_1027_;
}
}
v___jp_1027_:
{
if (v___y_1028_ == 0)
{
size_t v___x_1029_; size_t v___x_1030_; 
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1020_, v___x_1029_);
v_i_1020_ = v___x_1030_;
goto _start;
}
else
{
return v___x_1026_;
}
}
v___jp_1032_:
{
lean_object* v_kind_1033_; lean_object* v_config_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_kind_1033_ = lean_ctor_get(v___x_1023_, 2);
v_config_1034_ = lean_ctor_get(v___x_1023_, 3);
v___x_1035_ = l_Lake_LeanExe_keyword;
v___x_1036_ = lean_name_eq(v_kind_1033_, v___x_1035_);
if (v___x_1036_ == 0)
{
v___y_1028_ = v___x_1036_;
goto v___jp_1027_;
}
else
{
lean_object* v_root_1037_; uint8_t v___x_1038_; 
v_root_1037_ = lean_ctor_get(v_config_1034_, 2);
v___x_1038_ = lean_name_eq(v_root_1037_, v_mod_1018_);
v___y_1028_ = v___x_1038_;
goto v___jp_1027_;
}
}
}
else
{
uint8_t v___x_1042_; 
v___x_1042_ = 0;
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1043_, lean_object* v_as_1044_, lean_object* v_i_1045_, lean_object* v_stop_1046_){
_start:
{
size_t v_i_boxed_1047_; size_t v_stop_boxed_1048_; uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_i_boxed_1047_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_stop_boxed_1048_ = lean_unbox_usize(v_stop_1046_);
lean_dec(v_stop_1046_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1043_, v_as_1044_, v_i_boxed_1047_, v_stop_boxed_1048_);
lean_dec_ref(v_as_1044_);
lean_dec(v_mod_1043_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1051_, lean_object* v_self_1052_){
_start:
{
lean_object* v_targetDecls_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_targetDecls_1053_ = lean_ctor_get(v_self_1052_, 15);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_array_get_size(v_targetDecls_1053_);
v___x_1056_ = lean_nat_dec_lt(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
size_t v___x_1057_; size_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = lean_usize_of_nat(v___x_1055_);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1051_, v_targetDecls_1053_, v___x_1057_, v___x_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1060_, lean_object* v_self_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lake_Package_isBuildableModule(v_mod_1060_, v_self_1061_);
lean_dec_ref(v_self_1061_);
lean_dec(v_mod_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1064_){
_start:
{
lean_object* v_config_1066_; lean_object* v_dir_1067_; lean_object* v_buildDir_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_config_1066_ = lean_ctor_get(v_self_1064_, 6);
lean_inc_ref(v_config_1066_);
v_dir_1067_ = lean_ctor_get(v_self_1064_, 4);
lean_inc_ref(v_dir_1067_);
lean_dec_ref(v_self_1064_);
v_buildDir_1068_ = lean_ctor_get(v_config_1066_, 5);
lean_inc_ref(v_buildDir_1068_);
lean_dec_ref(v_config_1066_);
v___x_1069_ = l_System_FilePath_normalize(v_buildDir_1068_);
v___x_1070_ = l_Lake_joinRelative(v_dir_1067_, v___x_1069_);
v___x_1071_ = l_Lake_removeDirAllIfExists(v___x_1070_);
lean_dec_ref(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_Package_clean(v_self_1072_);
return v_res_1074_;
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
