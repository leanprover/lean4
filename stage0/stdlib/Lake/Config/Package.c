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
lean_inc_ref(v___y_358_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_357_);
v___x_365_ = lean_alloc_ctor(0, 23, 0);
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
lean_ctor_set(v___x_365_, 15, v___y_357_);
lean_ctor_set(v___x_365_, 16, v___y_361_);
lean_ctor_set(v___x_365_, 17, v___y_359_);
lean_ctor_set(v___x_365_, 18, v___y_360_);
lean_ctor_set(v___x_365_, 19, v___y_358_);
lean_ctor_set(v___x_365_, 20, v___y_362_);
lean_ctor_set(v___x_365_, 21, v_testDriver_363_);
lean_ctor_set(v___x_365_, 22, v_lintDriver_364_);
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
static uint64_t _init_l_Lake_Package_instHashable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_384_; uint64_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1723u);
v___x_385_ = lean_uint64_of_nat(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_386_){
_start:
{
lean_object* v_keyName_387_; 
v_keyName_387_ = lean_ctor_get(v_pkg_386_, 2);
if (lean_obj_tag(v_keyName_387_) == 0)
{
uint64_t v___x_388_; 
v___x_388_ = lean_uint64_once(&l_Lake_Package_instHashable___lam__0___closed__0, &l_Lake_Package_instHashable___lam__0___closed__0_once, _init_l_Lake_Package_instHashable___lam__0___closed__0);
return v___x_388_;
}
else
{
uint64_t v_hash_389_; 
v_hash_389_ = lean_ctor_get_uint64(v_keyName_387_, sizeof(void*)*2);
return v_hash_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_390_){
_start:
{
uint64_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lake_Package_instHashable___lam__0(v_pkg_390_);
lean_dec_ref(v_pkg_390_);
v_r_392_ = lean_box_uint64(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_395_, lean_object* v_p2_396_){
_start:
{
lean_object* v_wsIdx_397_; lean_object* v_wsIdx_398_; uint8_t v___x_399_; 
v_wsIdx_397_ = lean_ctor_get(v_p1_395_, 0);
v_wsIdx_398_ = lean_ctor_get(v_p2_396_, 0);
v___x_399_ = lean_nat_dec_eq(v_wsIdx_397_, v_wsIdx_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_400_, lean_object* v_p2_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lake_Package_instBEq___lam__0(v_p1_400_, v_p2_401_);
lean_dec_ref(v_p2_401_);
lean_dec_ref(v_p1_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_406_){
_start:
{
lean_object* v_baseName_407_; uint8_t v___x_408_; lean_object* v___x_409_; 
v_baseName_407_ = lean_ctor_get(v_self_406_, 1);
lean_inc(v_baseName_407_);
lean_dec_ref(v_self_406_);
v___x_408_ = 0;
v___x_409_ = l_Lean_Name_toString(v_baseName_407_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_410_){
_start:
{
lean_object* v_keyName_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_keyName_411_ = lean_ctor_get(v_x_410_, 2);
lean_inc(v_keyName_411_);
lean_dec_ref(v_x_410_);
v___x_412_ = 1;
v___x_413_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_411_, v___x_412_);
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_417_){
_start:
{
lean_object* v_baseName_418_; uint8_t v___x_419_; lean_object* v___x_420_; 
v_baseName_418_ = lean_ctor_get(v_x_417_, 1);
lean_inc(v_baseName_418_);
lean_dec_ref(v_x_417_);
v___x_419_ = 0;
v___x_420_ = l_Lean_Name_toString(v_baseName_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_423_){
_start:
{
lean_object* v_baseName_424_; 
v_baseName_424_ = lean_ctor_get(v_self_423_, 1);
lean_inc(v_baseName_424_);
return v_baseName_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_Package_name(v_self_425_);
lean_dec_ref(v_self_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_427_){
_start:
{
lean_object* v_origName_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
v_origName_428_ = lean_ctor_get(v_self_427_, 3);
lean_inc(v_origName_428_);
lean_dec_ref(v_self_427_);
v___x_429_ = 0;
v___x_430_ = l_Lean_Name_toString(v_origName_428_, v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_unsigned_to_nat(16u);
v___x_433_ = lean_mk_array(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_437_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___f_438_; lean_object* v___f_439_; lean_object* v___x_440_; 
v___f_438_ = ((lean_object*)(l_Lake_Package_instBEq___closed__0));
v___f_439_ = ((lean_object*)(l_Lake_Package_instHashable___closed__0));
v___x_440_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_439_, v___f_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object* v_self_442_){
_start:
{
lean_inc_ref(v_self_442_);
return v_self_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object* v_self_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_443_);
lean_dec_ref(v_self_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_446_){
_start:
{
lean_object* v___f_447_; 
v___f_447_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___closed__0));
return v___f_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_NPackage_instCoeOutPackage(v_n_448_);
lean_dec(v_n_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_450_){
_start:
{
lean_inc_ref(v_pkg_450_);
return v_pkg_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_451_);
lean_dec_ref(v_pkg_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___y_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_459_, v___y_460_, v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v_x_459_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_465_){
_start:
{
lean_object* v___f_466_; 
v___f_466_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_467_);
lean_dec(v_pkgName_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_469_){
_start:
{
lean_object* v___f_470_; 
v___f_470_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lake_instInhabitedPostUpdateHook(v_a_471_);
lean_dec(v_a_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_473_){
_start:
{
lean_inc_ref(v_a_473_);
return v_a_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_474_);
lean_dec_ref(v_a_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_476_, lean_object* v_a_477_){
_start:
{
lean_inc_ref(v_a_477_);
return v_a_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_478_, v_a_479_);
lean_dec_ref(v_a_479_);
lean_dec(v_name_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_482_, 0, v_name_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_483_){
_start:
{
lean_inc(v_a_483_);
return v_a_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_484_);
lean_dec(v_a_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_486_, lean_object* v_a_487_){
_start:
{
lean_inc(v_a_487_);
return v_a_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec(v_name_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_492_, 0, v_name_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_493_){
_start:
{
lean_inc_ref(v_inst_493_);
return v_inst_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_494_);
lean_dec_ref(v_inst_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_496_, lean_object* v_inst_497_){
_start:
{
lean_inc_ref(v_inst_497_);
return v_inst_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_498_, lean_object* v_inst_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_498_, v_inst_499_);
lean_dec_ref(v_inst_499_);
lean_dec(v_name_498_);
return v_res_500_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_508_){
_start:
{
lean_object* v_wsIdx_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_wsIdx_509_ = lean_ctor_get(v_self_508_, 0);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_nat_dec_eq(v_wsIdx_509_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Lake_Package_isRoot(v_self_512_);
lean_dec_ref(v_self_512_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_515_){
_start:
{
lean_object* v_config_516_; uint8_t v_bootstrap_517_; 
v_config_516_ = lean_ctor_get(v_self_515_, 6);
v_bootstrap_517_ = lean_ctor_get_uint8(v_config_516_, sizeof(void*)*27);
return v_bootstrap_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lake_Package_bootstrap(v_self_518_);
lean_dec_ref(v_self_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_521_){
_start:
{
lean_object* v_config_522_; uint8_t v_bootstrap_523_; 
v_config_522_ = lean_ctor_get(v_self_521_, 6);
v_bootstrap_523_ = lean_ctor_get_uint8(v_config_522_, sizeof(void*)*27);
if (v_bootstrap_523_ == 0)
{
lean_object* v_origName_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_origName_524_ = lean_ctor_get(v_self_521_, 3);
lean_inc(v_origName_524_);
lean_dec_ref(v_self_521_);
v___x_525_ = l_Lean_Name_toString(v_origName_524_, v_bootstrap_523_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_self_521_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_528_){
_start:
{
lean_object* v_config_529_; lean_object* v_version_530_; 
v_config_529_ = lean_ctor_get(v_self_528_, 6);
v_version_530_ = lean_ctor_get(v_config_529_, 16);
lean_inc_ref(v_version_530_);
return v_version_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lake_Package_version(v_self_531_);
lean_dec_ref(v_self_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_533_){
_start:
{
lean_object* v_config_534_; lean_object* v_versionTags_535_; 
v_config_534_ = lean_ctor_get(v_self_533_, 6);
v_versionTags_535_ = lean_ctor_get(v_config_534_, 17);
lean_inc_ref(v_versionTags_535_);
return v_versionTags_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lake_Package_versionTags(v_self_536_);
lean_dec_ref(v_self_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_538_){
_start:
{
lean_object* v_config_539_; lean_object* v_description_540_; 
v_config_539_ = lean_ctor_get(v_self_538_, 6);
v_description_540_ = lean_ctor_get(v_config_539_, 18);
lean_inc_ref(v_description_540_);
return v_description_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lake_Package_description(v_self_541_);
lean_dec_ref(v_self_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_543_){
_start:
{
lean_object* v_config_544_; lean_object* v_keywords_545_; 
v_config_544_ = lean_ctor_get(v_self_543_, 6);
v_keywords_545_ = lean_ctor_get(v_config_544_, 19);
lean_inc_ref(v_keywords_545_);
return v_keywords_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lake_Package_keywords(v_self_546_);
lean_dec_ref(v_self_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_548_){
_start:
{
lean_object* v_config_549_; lean_object* v_homepage_550_; 
v_config_549_ = lean_ctor_get(v_self_548_, 6);
v_homepage_550_ = lean_ctor_get(v_config_549_, 20);
lean_inc_ref(v_homepage_550_);
return v_homepage_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lake_Package_homepage(v_self_551_);
lean_dec_ref(v_self_551_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_553_){
_start:
{
lean_object* v_config_554_; uint8_t v_reservoir_555_; 
v_config_554_ = lean_ctor_get(v_self_553_, 6);
v_reservoir_555_ = lean_ctor_get_uint8(v_config_554_, sizeof(void*)*27 + 3);
return v_reservoir_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lake_Package_reservoir(v_self_556_);
lean_dec_ref(v_self_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_559_){
_start:
{
lean_object* v_config_560_; lean_object* v_license_561_; 
v_config_560_ = lean_ctor_get(v_self_559_, 6);
v_license_561_ = lean_ctor_get(v_config_560_, 21);
lean_inc_ref(v_license_561_);
return v_license_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lake_Package_license(v_self_562_);
lean_dec_ref(v_self_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_584_){
_start:
{
lean_object* v_config_585_; lean_object* v_licenseFiles_586_; lean_object* v___f_587_; lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
v_config_585_ = lean_ctor_get(v_self_584_, 6);
lean_inc_ref(v_config_585_);
lean_dec_ref(v_self_584_);
v_licenseFiles_586_ = lean_ctor_get(v_config_585_, 22);
lean_inc_ref(v_licenseFiles_586_);
lean_dec_ref(v_config_585_);
v___f_587_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_588_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_589_ = lean_array_size(v_licenseFiles_586_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_588_, v___f_587_, v_sz_589_, v___x_590_, v_licenseFiles_586_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_System_FilePath_normalize(v_x_593_);
v___x_595_ = l_Lake_joinRelative(v_dir_592_, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_596_){
_start:
{
lean_object* v_config_597_; lean_object* v_dir_598_; lean_object* v_licenseFiles_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; size_t v_sz_603_; size_t v___x_604_; lean_object* v___x_605_; size_t v_sz_606_; lean_object* v___x_607_; 
v_config_597_ = lean_ctor_get(v_self_596_, 6);
lean_inc_ref(v_config_597_);
v_dir_598_ = lean_ctor_get(v_self_596_, 4);
lean_inc_ref(v_dir_598_);
lean_dec_ref(v_self_596_);
v_licenseFiles_599_ = lean_ctor_get(v_config_597_, 22);
lean_inc_ref(v_licenseFiles_599_);
lean_dec_ref(v_config_597_);
v___f_600_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_601_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_601_, 0, v_dir_598_);
v___x_602_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_603_ = lean_array_size(v_licenseFiles_599_);
v___x_604_ = ((size_t)0ULL);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_602_, v___f_600_, v_sz_603_, v___x_604_, v_licenseFiles_599_);
v_sz_606_ = lean_array_size(v___x_605_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_602_, v___f_601_, v_sz_606_, v___x_604_, v___x_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_608_){
_start:
{
lean_object* v_config_609_; lean_object* v_readmeFile_610_; lean_object* v___x_611_; 
v_config_609_ = lean_ctor_get(v_self_608_, 6);
lean_inc_ref(v_config_609_);
lean_dec_ref(v_self_608_);
v_readmeFile_610_ = lean_ctor_get(v_config_609_, 23);
lean_inc_ref(v_readmeFile_610_);
lean_dec_ref(v_config_609_);
v___x_611_ = l_System_FilePath_normalize(v_readmeFile_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_612_){
_start:
{
lean_object* v_config_613_; lean_object* v_dir_614_; lean_object* v_readmeFile_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_config_613_ = lean_ctor_get(v_self_612_, 6);
lean_inc_ref(v_config_613_);
v_dir_614_ = lean_ctor_get(v_self_612_, 4);
lean_inc_ref(v_dir_614_);
lean_dec_ref(v_self_612_);
v_readmeFile_615_ = lean_ctor_get(v_config_613_, 23);
lean_inc_ref(v_readmeFile_615_);
lean_dec_ref(v_config_613_);
v___x_616_ = l_System_FilePath_normalize(v_readmeFile_615_);
v___x_617_ = l_Lake_joinRelative(v_dir_614_, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lake_defaultLakeDir;
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lake_Package_relLakeDir(v_x_620_);
lean_dec_ref(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_622_){
_start:
{
lean_object* v_dir_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_dir_623_ = lean_ctor_get(v_self_622_, 4);
lean_inc_ref(v_dir_623_);
lean_dec_ref(v_self_622_);
v___x_624_ = l_Lake_defaultLakeDir;
v___x_625_ = l_Lake_joinRelative(v_dir_623_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_626_){
_start:
{
lean_object* v_config_627_; lean_object* v_toWorkspaceConfig_628_; lean_object* v___x_629_; 
v_config_627_ = lean_ctor_get(v_self_626_, 6);
lean_inc_ref(v_config_627_);
lean_dec_ref(v_self_626_);
v_toWorkspaceConfig_628_ = lean_ctor_get(v_config_627_, 0);
lean_inc_ref(v_toWorkspaceConfig_628_);
lean_dec_ref(v_config_627_);
v___x_629_ = l_System_FilePath_normalize(v_toWorkspaceConfig_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_630_){
_start:
{
lean_object* v_config_631_; lean_object* v_dir_632_; lean_object* v_toWorkspaceConfig_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_config_631_ = lean_ctor_get(v_self_630_, 6);
lean_inc_ref(v_config_631_);
v_dir_632_ = lean_ctor_get(v_self_630_, 4);
lean_inc_ref(v_dir_632_);
lean_dec_ref(v_self_630_);
v_toWorkspaceConfig_633_ = lean_ctor_get(v_config_631_, 0);
lean_inc_ref(v_toWorkspaceConfig_633_);
lean_dec_ref(v_config_631_);
v___x_634_ = l_System_FilePath_normalize(v_toWorkspaceConfig_633_);
v___x_635_ = l_Lake_joinRelative(v_dir_632_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_636_){
_start:
{
lean_object* v_dir_637_; lean_object* v_relManifestFile_638_; lean_object* v___x_639_; 
v_dir_637_ = lean_ctor_get(v_self_636_, 4);
lean_inc_ref(v_dir_637_);
v_relManifestFile_638_ = lean_ctor_get(v_self_636_, 9);
lean_inc_ref(v_relManifestFile_638_);
lean_dec_ref(v_self_636_);
v___x_639_ = l_Lake_joinRelative(v_dir_637_, v_relManifestFile_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_640_){
_start:
{
lean_object* v_config_641_; lean_object* v_dir_642_; lean_object* v_buildDir_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_config_641_ = lean_ctor_get(v_self_640_, 6);
lean_inc_ref(v_config_641_);
v_dir_642_ = lean_ctor_get(v_self_640_, 4);
lean_inc_ref(v_dir_642_);
lean_dec_ref(v_self_640_);
v_buildDir_643_ = lean_ctor_get(v_config_641_, 5);
lean_inc_ref(v_buildDir_643_);
lean_dec_ref(v_config_641_);
v___x_644_ = l_System_FilePath_normalize(v_buildDir_643_);
v___x_645_ = l_Lake_joinRelative(v_dir_642_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_646_){
_start:
{
lean_object* v_config_647_; lean_object* v_testDriverArgs_648_; 
v_config_647_ = lean_ctor_get(v_self_646_, 6);
v_testDriverArgs_648_ = lean_ctor_get(v_config_647_, 13);
lean_inc_ref(v_testDriverArgs_648_);
return v_testDriverArgs_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lake_Package_testDriverArgs(v_self_649_);
lean_dec_ref(v_self_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_651_){
_start:
{
lean_object* v_config_652_; lean_object* v_lintDriverArgs_653_; 
v_config_652_ = lean_ctor_get(v_self_651_, 6);
v_lintDriverArgs_653_ = lean_ctor_get(v_config_652_, 15);
lean_inc_ref(v_lintDriverArgs_653_);
return v_lintDriverArgs_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_Package_lintDriverArgs(v_self_654_);
lean_dec_ref(v_self_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_656_){
_start:
{
lean_object* v_config_657_; lean_object* v_extraDepTargets_658_; 
v_config_657_ = lean_ctor_get(v_self_656_, 6);
v_extraDepTargets_658_ = lean_ctor_get(v_config_657_, 2);
lean_inc_ref(v_extraDepTargets_658_);
return v_extraDepTargets_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lake_Package_extraDepTargets(v_self_659_);
lean_dec_ref(v_self_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_661_){
_start:
{
lean_object* v_config_662_; lean_object* v_toLeanConfig_663_; lean_object* v_platformIndependent_664_; 
v_config_662_ = lean_ctor_get(v_self_661_, 6);
v_toLeanConfig_663_ = lean_ctor_get(v_config_662_, 1);
v_platformIndependent_664_ = lean_ctor_get(v_toLeanConfig_663_, 10);
lean_inc(v_platformIndependent_664_);
return v_platformIndependent_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_Package_platformIndependent(v_self_665_);
lean_dec_ref(v_self_665_);
return v_res_666_;
}
}
static lean_object* _init_l_Lake_Package_isPlatformIndependent___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___f_668_; 
v___x_667_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_668_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_668_, 0, v___x_667_);
return v___f_668_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_672_){
_start:
{
lean_object* v_config_673_; lean_object* v_toLeanConfig_674_; lean_object* v_platformIndependent_675_; lean_object* v___f_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_config_673_ = lean_ctor_get(v_self_672_, 6);
lean_inc_ref(v_config_673_);
lean_dec_ref(v_self_672_);
v_toLeanConfig_674_ = lean_ctor_get(v_config_673_, 1);
lean_inc_ref(v_toLeanConfig_674_);
lean_dec_ref(v_config_673_);
v_platformIndependent_675_ = lean_ctor_get(v_toLeanConfig_674_, 10);
lean_inc(v_platformIndependent_675_);
lean_dec_ref(v_toLeanConfig_674_);
v___f_676_ = lean_obj_once(&l_Lake_Package_isPlatformIndependent___closed__0, &l_Lake_Package_isPlatformIndependent___closed__0_once, _init_l_Lake_Package_isPlatformIndependent___closed__0);
v___x_677_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_678_ = l_Option_instBEq_beq___redArg(v___f_676_, v_platformIndependent_675_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Lake_Package_isPlatformIndependent(v_self_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_682_){
_start:
{
lean_object* v_config_683_; uint8_t v_fixedToolchain_684_; 
v_config_683_ = lean_ctor_get(v_self_682_, 6);
v_fixedToolchain_684_ = lean_ctor_get_uint8(v_config_683_, sizeof(void*)*27 + 6);
return v_fixedToolchain_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Lake_Package_fixedToolchain(v_self_685_);
lean_dec_ref(v_self_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_688_){
_start:
{
lean_object* v_config_689_; lean_object* v_releaseRepo_690_; 
v_config_689_ = lean_ctor_get(v_self_688_, 6);
v_releaseRepo_690_ = lean_ctor_get(v_config_689_, 10);
lean_inc(v_releaseRepo_690_);
return v_releaseRepo_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lake_Package_releaseRepo_x3f(v_self_691_);
lean_dec_ref(v_self_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_693_){
_start:
{
lean_object* v_remoteUrl_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_remoteUrl_694_ = lean_ctor_get(v_self_693_, 11);
v___x_695_ = lean_string_utf8_byte_size(v_remoteUrl_694_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
return v___x_698_;
}
else
{
lean_object* v___x_699_; 
lean_inc_ref(v_remoteUrl_694_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_remoteUrl_694_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lake_Package_remoteUrl_x3f(v_self_700_);
lean_dec_ref(v_self_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_702_){
_start:
{
lean_object* v_dir_703_; lean_object* v_buildArchive_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_dir_703_ = lean_ctor_get(v_self_702_, 4);
lean_inc_ref(v_dir_703_);
v_buildArchive_704_ = lean_ctor_get(v_self_702_, 20);
lean_inc_ref(v_buildArchive_704_);
lean_dec_ref(v_self_702_);
v___x_705_ = l_Lake_defaultLakeDir;
v___x_706_ = l_Lake_joinRelative(v_dir_703_, v___x_705_);
v___x_707_ = l_Lake_joinRelative(v___x_706_, v_buildArchive_704_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_709_){
_start:
{
lean_object* v_dir_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_dir_710_ = lean_ctor_get(v_self_709_, 4);
lean_inc_ref(v_dir_710_);
lean_dec_ref(v_self_709_);
v___x_711_ = l_Lake_defaultLakeDir;
v___x_712_ = l_Lake_joinRelative(v_dir_710_, v___x_711_);
v___x_713_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_714_ = l_Lake_joinRelative(v___x_712_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_715_){
_start:
{
lean_object* v_config_716_; uint8_t v_preferReleaseBuild_717_; 
v_config_716_ = lean_ctor_get(v_self_715_, 6);
v_preferReleaseBuild_717_ = lean_ctor_get_uint8(v_config_716_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lake_Package_preferReleaseBuild(v_self_718_);
lean_dec_ref(v_self_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_721_){
_start:
{
lean_object* v_config_722_; uint8_t v_precompileModules_723_; 
v_config_722_ = lean_ctor_get(v_self_721_, 6);
v_precompileModules_723_ = lean_ctor_get_uint8(v_config_722_, sizeof(void*)*27 + 1);
return v_precompileModules_723_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Lake_Package_precompileModules(v_self_724_);
lean_dec_ref(v_self_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_727_){
_start:
{
lean_object* v_config_728_; lean_object* v_moreGlobalServerArgs_729_; 
v_config_728_ = lean_ctor_get(v_self_727_, 6);
v_moreGlobalServerArgs_729_ = lean_ctor_get(v_config_728_, 3);
lean_inc_ref(v_moreGlobalServerArgs_729_);
return v_moreGlobalServerArgs_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lake_Package_moreGlobalServerArgs(v_self_730_);
lean_dec_ref(v_self_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_732_){
_start:
{
lean_object* v_config_733_; lean_object* v_toLeanConfig_734_; lean_object* v_leanOptions_735_; lean_object* v_moreServerOptions_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_config_733_ = lean_ctor_get(v_self_732_, 6);
v_toLeanConfig_734_ = lean_ctor_get(v_config_733_, 1);
v_leanOptions_735_ = lean_ctor_get(v_toLeanConfig_734_, 0);
v_moreServerOptions_736_ = lean_ctor_get(v_toLeanConfig_734_, 4);
v___x_737_ = l_Lean_LeanOptions_ofArray(v_leanOptions_735_);
v___x_738_ = l_Lean_LeanOptions_appendArray(v___x_737_, v_moreServerOptions_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lake_Package_moreServerOptions(v_self_739_);
lean_dec_ref(v_self_739_);
return v_res_740_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_741_){
_start:
{
lean_object* v_config_742_; lean_object* v_toLeanConfig_743_; uint8_t v_buildType_744_; 
v_config_742_ = lean_ctor_get(v_self_741_, 6);
v_toLeanConfig_743_ = lean_ctor_get(v_config_742_, 1);
v_buildType_744_ = lean_ctor_get_uint8(v_toLeanConfig_743_, sizeof(void*)*13);
return v_buildType_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Lake_Package_buildType(v_self_745_);
lean_dec_ref(v_self_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_748_){
_start:
{
lean_object* v_config_749_; lean_object* v_toLeanConfig_750_; uint8_t v_backend_751_; 
v_config_749_ = lean_ctor_get(v_self_748_, 6);
v_toLeanConfig_750_ = lean_ctor_get(v_config_749_, 1);
v_backend_751_ = lean_ctor_get_uint8(v_toLeanConfig_750_, sizeof(void*)*13 + 1);
return v_backend_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_Lake_Package_backend(v_self_752_);
lean_dec_ref(v_self_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_755_){
_start:
{
lean_object* v_config_756_; uint8_t v_allowImportAll_757_; 
v_config_756_ = lean_ctor_get(v_self_755_, 6);
v_allowImportAll_757_ = lean_ctor_get_uint8(v_config_756_, sizeof(void*)*27 + 5);
return v_allowImportAll_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lake_Package_allowImportAll(v_self_758_);
lean_dec_ref(v_self_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_761_){
_start:
{
lean_object* v_config_762_; lean_object* v_toLeanConfig_763_; lean_object* v_dynlibs_764_; 
v_config_762_ = lean_ctor_get(v_self_761_, 6);
v_toLeanConfig_763_ = lean_ctor_get(v_config_762_, 1);
v_dynlibs_764_ = lean_ctor_get(v_toLeanConfig_763_, 11);
lean_inc_ref(v_dynlibs_764_);
return v_dynlibs_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lake_Package_dynlibs(v_self_765_);
lean_dec_ref(v_self_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_767_){
_start:
{
lean_object* v_config_768_; lean_object* v_toLeanConfig_769_; lean_object* v_plugins_770_; 
v_config_768_ = lean_ctor_get(v_self_767_, 6);
v_toLeanConfig_769_ = lean_ctor_get(v_config_768_, 1);
v_plugins_770_ = lean_ctor_get(v_toLeanConfig_769_, 12);
lean_inc_ref(v_plugins_770_);
return v_plugins_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lake_Package_plugins(v_self_771_);
lean_dec_ref(v_self_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_773_){
_start:
{
lean_object* v_config_774_; lean_object* v_toLeanConfig_775_; lean_object* v_leanOptions_776_; lean_object* v___x_777_; 
v_config_774_ = lean_ctor_get(v_self_773_, 6);
v_toLeanConfig_775_ = lean_ctor_get(v_config_774_, 1);
v_leanOptions_776_ = lean_ctor_get(v_toLeanConfig_775_, 0);
v___x_777_ = l_Lean_LeanOptions_ofArray(v_leanOptions_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_Package_leanOptions(v_self_778_);
lean_dec_ref(v_self_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_780_){
_start:
{
lean_object* v_config_781_; lean_object* v_toLeanConfig_782_; lean_object* v_moreLeanArgs_783_; 
v_config_781_ = lean_ctor_get(v_self_780_, 6);
v_toLeanConfig_782_ = lean_ctor_get(v_config_781_, 1);
v_moreLeanArgs_783_ = lean_ctor_get(v_toLeanConfig_782_, 1);
lean_inc_ref(v_moreLeanArgs_783_);
return v_moreLeanArgs_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_Package_moreLeanArgs(v_self_784_);
lean_dec_ref(v_self_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_786_){
_start:
{
lean_object* v_config_787_; lean_object* v_toLeanConfig_788_; lean_object* v_weakLeanArgs_789_; 
v_config_787_ = lean_ctor_get(v_self_786_, 6);
v_toLeanConfig_788_ = lean_ctor_get(v_config_787_, 1);
v_weakLeanArgs_789_ = lean_ctor_get(v_toLeanConfig_788_, 2);
lean_inc_ref(v_weakLeanArgs_789_);
return v_weakLeanArgs_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_Package_weakLeanArgs(v_self_790_);
lean_dec_ref(v_self_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_792_){
_start:
{
lean_object* v_config_793_; lean_object* v_toLeanConfig_794_; lean_object* v_moreLeancArgs_795_; 
v_config_793_ = lean_ctor_get(v_self_792_, 6);
v_toLeanConfig_794_ = lean_ctor_get(v_config_793_, 1);
v_moreLeancArgs_795_ = lean_ctor_get(v_toLeanConfig_794_, 3);
lean_inc_ref(v_moreLeancArgs_795_);
return v_moreLeancArgs_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lake_Package_moreLeancArgs(v_self_796_);
lean_dec_ref(v_self_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_798_){
_start:
{
lean_object* v_config_799_; lean_object* v_toLeanConfig_800_; lean_object* v_weakLeancArgs_801_; 
v_config_799_ = lean_ctor_get(v_self_798_, 6);
v_toLeanConfig_800_ = lean_ctor_get(v_config_799_, 1);
v_weakLeancArgs_801_ = lean_ctor_get(v_toLeanConfig_800_, 5);
lean_inc_ref(v_weakLeancArgs_801_);
return v_weakLeancArgs_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lake_Package_weakLeancArgs(v_self_802_);
lean_dec_ref(v_self_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_804_){
_start:
{
lean_object* v_config_805_; lean_object* v_toLeanConfig_806_; lean_object* v_moreLinkObjs_807_; 
v_config_805_ = lean_ctor_get(v_self_804_, 6);
v_toLeanConfig_806_ = lean_ctor_get(v_config_805_, 1);
v_moreLinkObjs_807_ = lean_ctor_get(v_toLeanConfig_806_, 6);
lean_inc_ref(v_moreLinkObjs_807_);
return v_moreLinkObjs_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lake_Package_moreLinkObjs(v_self_808_);
lean_dec_ref(v_self_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_810_){
_start:
{
lean_object* v_config_811_; lean_object* v_toLeanConfig_812_; lean_object* v_moreLinkLibs_813_; 
v_config_811_ = lean_ctor_get(v_self_810_, 6);
v_toLeanConfig_812_ = lean_ctor_get(v_config_811_, 1);
v_moreLinkLibs_813_ = lean_ctor_get(v_toLeanConfig_812_, 7);
lean_inc_ref(v_moreLinkLibs_813_);
return v_moreLinkLibs_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lake_Package_moreLinkLibs(v_self_814_);
lean_dec_ref(v_self_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_816_){
_start:
{
lean_object* v_config_817_; lean_object* v_toLeanConfig_818_; lean_object* v_moreLinkArgs_819_; 
v_config_817_ = lean_ctor_get(v_self_816_, 6);
v_toLeanConfig_818_ = lean_ctor_get(v_config_817_, 1);
v_moreLinkArgs_819_ = lean_ctor_get(v_toLeanConfig_818_, 8);
lean_inc_ref(v_moreLinkArgs_819_);
return v_moreLinkArgs_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lake_Package_moreLinkArgs(v_self_820_);
lean_dec_ref(v_self_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_822_){
_start:
{
lean_object* v_config_823_; lean_object* v_toLeanConfig_824_; lean_object* v_weakLinkArgs_825_; 
v_config_823_ = lean_ctor_get(v_self_822_, 6);
v_toLeanConfig_824_ = lean_ctor_get(v_config_823_, 1);
v_weakLinkArgs_825_ = lean_ctor_get(v_toLeanConfig_824_, 9);
lean_inc_ref(v_weakLinkArgs_825_);
return v_weakLinkArgs_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lake_Package_weakLinkArgs(v_self_826_);
lean_dec_ref(v_self_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_828_){
_start:
{
lean_object* v_config_829_; lean_object* v_dir_830_; lean_object* v_srcDir_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_config_829_ = lean_ctor_get(v_self_828_, 6);
lean_inc_ref(v_config_829_);
v_dir_830_ = lean_ctor_get(v_self_828_, 4);
lean_inc_ref(v_dir_830_);
lean_dec_ref(v_self_828_);
v_srcDir_831_ = lean_ctor_get(v_config_829_, 4);
lean_inc_ref(v_srcDir_831_);
lean_dec_ref(v_config_829_);
v___x_832_ = l_System_FilePath_normalize(v_srcDir_831_);
v___x_833_ = l_Lake_joinRelative(v_dir_830_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_834_){
_start:
{
lean_object* v_config_835_; lean_object* v_dir_836_; lean_object* v_srcDir_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_config_835_ = lean_ctor_get(v_self_834_, 6);
lean_inc_ref(v_config_835_);
v_dir_836_ = lean_ctor_get(v_self_834_, 4);
lean_inc_ref(v_dir_836_);
lean_dec_ref(v_self_834_);
v_srcDir_837_ = lean_ctor_get(v_config_835_, 4);
lean_inc_ref(v_srcDir_837_);
lean_dec_ref(v_config_835_);
v___x_838_ = l_System_FilePath_normalize(v_srcDir_837_);
v___x_839_ = l_Lake_joinRelative(v_dir_836_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_840_){
_start:
{
lean_object* v_config_841_; lean_object* v_dir_842_; lean_object* v_buildDir_843_; lean_object* v_leanLibDir_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_config_841_ = lean_ctor_get(v_self_840_, 6);
lean_inc_ref(v_config_841_);
v_dir_842_ = lean_ctor_get(v_self_840_, 4);
lean_inc_ref(v_dir_842_);
lean_dec_ref(v_self_840_);
v_buildDir_843_ = lean_ctor_get(v_config_841_, 5);
lean_inc_ref(v_buildDir_843_);
v_leanLibDir_844_ = lean_ctor_get(v_config_841_, 6);
lean_inc_ref(v_leanLibDir_844_);
lean_dec_ref(v_config_841_);
v___x_845_ = l_System_FilePath_normalize(v_buildDir_843_);
v___x_846_ = l_Lake_joinRelative(v_dir_842_, v___x_845_);
v___x_847_ = l_System_FilePath_normalize(v_leanLibDir_844_);
v___x_848_ = l_Lake_joinRelative(v___x_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_849_){
_start:
{
lean_object* v_config_850_; lean_object* v_dir_851_; lean_object* v_buildDir_852_; lean_object* v_nativeLibDir_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_config_850_ = lean_ctor_get(v_self_849_, 6);
lean_inc_ref(v_config_850_);
v_dir_851_ = lean_ctor_get(v_self_849_, 4);
lean_inc_ref(v_dir_851_);
lean_dec_ref(v_self_849_);
v_buildDir_852_ = lean_ctor_get(v_config_850_, 5);
lean_inc_ref(v_buildDir_852_);
v_nativeLibDir_853_ = lean_ctor_get(v_config_850_, 7);
lean_inc_ref(v_nativeLibDir_853_);
lean_dec_ref(v_config_850_);
v___x_854_ = l_System_FilePath_normalize(v_buildDir_852_);
v___x_855_ = l_Lake_joinRelative(v_dir_851_, v___x_854_);
v___x_856_ = l_System_FilePath_normalize(v_nativeLibDir_853_);
v___x_857_ = l_Lake_joinRelative(v___x_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_858_){
_start:
{
lean_object* v_config_859_; lean_object* v_dir_860_; lean_object* v_buildDir_861_; lean_object* v_nativeLibDir_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_config_859_ = lean_ctor_get(v_self_858_, 6);
lean_inc_ref(v_config_859_);
v_dir_860_ = lean_ctor_get(v_self_858_, 4);
lean_inc_ref(v_dir_860_);
lean_dec_ref(v_self_858_);
v_buildDir_861_ = lean_ctor_get(v_config_859_, 5);
lean_inc_ref(v_buildDir_861_);
v_nativeLibDir_862_ = lean_ctor_get(v_config_859_, 7);
lean_inc_ref(v_nativeLibDir_862_);
lean_dec_ref(v_config_859_);
v___x_863_ = l_System_FilePath_normalize(v_buildDir_861_);
v___x_864_ = l_Lake_joinRelative(v_dir_860_, v___x_863_);
v___x_865_ = l_System_FilePath_normalize(v_nativeLibDir_862_);
v___x_866_ = l_Lake_joinRelative(v___x_864_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_867_){
_start:
{
lean_object* v_config_868_; lean_object* v_dir_869_; lean_object* v_buildDir_870_; lean_object* v_binDir_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_config_868_ = lean_ctor_get(v_self_867_, 6);
lean_inc_ref(v_config_868_);
v_dir_869_ = lean_ctor_get(v_self_867_, 4);
lean_inc_ref(v_dir_869_);
lean_dec_ref(v_self_867_);
v_buildDir_870_ = lean_ctor_get(v_config_868_, 5);
lean_inc_ref(v_buildDir_870_);
v_binDir_871_ = lean_ctor_get(v_config_868_, 8);
lean_inc_ref(v_binDir_871_);
lean_dec_ref(v_config_868_);
v___x_872_ = l_System_FilePath_normalize(v_buildDir_870_);
v___x_873_ = l_Lake_joinRelative(v_dir_869_, v___x_872_);
v___x_874_ = l_System_FilePath_normalize(v_binDir_871_);
v___x_875_ = l_Lake_joinRelative(v___x_873_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_876_){
_start:
{
lean_object* v_config_877_; lean_object* v_dir_878_; lean_object* v_buildDir_879_; lean_object* v_irDir_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_config_877_ = lean_ctor_get(v_self_876_, 6);
lean_inc_ref(v_config_877_);
v_dir_878_ = lean_ctor_get(v_self_876_, 4);
lean_inc_ref(v_dir_878_);
lean_dec_ref(v_self_876_);
v_buildDir_879_ = lean_ctor_get(v_config_877_, 5);
lean_inc_ref(v_buildDir_879_);
v_irDir_880_ = lean_ctor_get(v_config_877_, 9);
lean_inc_ref(v_irDir_880_);
lean_dec_ref(v_config_877_);
v___x_881_ = l_System_FilePath_normalize(v_buildDir_879_);
v___x_882_ = l_Lake_joinRelative(v_dir_878_, v___x_881_);
v___x_883_ = l_System_FilePath_normalize(v_irDir_880_);
v___x_884_ = l_Lake_joinRelative(v___x_882_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_885_){
_start:
{
lean_object* v_config_886_; uint8_t v_libPrefixOnWindows_887_; 
v_config_886_ = lean_ctor_get(v_self_885_, 6);
v_libPrefixOnWindows_887_ = lean_ctor_get_uint8(v_config_886_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_887_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Lake_Package_libPrefixOnWindows(v_self_888_);
lean_dec_ref(v_self_888_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_891_){
_start:
{
lean_object* v_config_892_; lean_object* v_enableArtifactCache_x3f_893_; 
v_config_892_ = lean_ctor_get(v_self_891_, 6);
v_enableArtifactCache_x3f_893_ = lean_ctor_get(v_config_892_, 24);
lean_inc(v_enableArtifactCache_x3f_893_);
return v_enableArtifactCache_x3f_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lake_Package_enableArtifactCache_x3f(v_self_894_);
lean_dec_ref(v_self_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_896_){
_start:
{
lean_object* v_config_897_; lean_object* v_restoreAllArtifacts_x3f_898_; 
v_config_897_ = lean_ctor_get(v_self_896_, 6);
v_restoreAllArtifacts_x3f_898_ = lean_ctor_get(v_config_897_, 25);
lean_inc(v_restoreAllArtifacts_x3f_898_);
return v_restoreAllArtifacts_x3f_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_899_);
lean_dec_ref(v_self_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_901_){
_start:
{
lean_object* v_baseName_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v_baseName_902_ = lean_ctor_get(v_self_901_, 1);
lean_inc(v_baseName_902_);
lean_dec_ref(v_self_901_);
v___x_903_ = 0;
v___x_904_ = l_Lean_Name_toString(v_baseName_902_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_906_){
_start:
{
lean_object* v_origName_907_; lean_object* v_scope_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_origName_907_ = lean_ctor_get(v_self_906_, 3);
lean_inc(v_origName_907_);
v_scope_908_ = lean_ctor_get(v_self_906_, 10);
lean_inc_ref(v_scope_908_);
lean_dec_ref(v_self_906_);
v___x_909_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_910_ = lean_string_append(v_scope_908_, v___x_909_);
v___x_911_ = 0;
v___x_912_ = l_Lean_Name_toString(v_origName_907_, v___x_911_);
v___x_913_ = lean_string_append(v___x_910_, v___x_912_);
lean_dec_ref(v___x_912_);
v___x_914_ = l_Lake_CacheServiceScope_ofString(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_915_){
_start:
{
lean_object* v_scope_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_scope_916_ = lean_ctor_get(v_self_915_, 10);
v___x_917_ = lean_string_utf8_byte_size(v_scope_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_915_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v_self_915_);
v___x_922_ = lean_box(0);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_923_, lean_object* v_k_924_){
_start:
{
if (lean_obj_tag(v_t_923_) == 0)
{
lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v_l_927_; lean_object* v_r_928_; uint8_t v___x_929_; 
v_k_925_ = lean_ctor_get(v_t_923_, 1);
v_v_926_ = lean_ctor_get(v_t_923_, 2);
v_l_927_ = lean_ctor_get(v_t_923_, 3);
v_r_928_ = lean_ctor_get(v_t_923_, 4);
v___x_929_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_924_, v_k_925_);
switch(v___x_929_)
{
case 0:
{
v_t_923_ = v_l_927_;
goto _start;
}
case 1:
{
lean_object* v___x_931_; 
lean_inc(v_v_926_);
v___x_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_931_, 0, v_v_926_);
return v___x_931_;
}
default: 
{
v_t_923_ = v_r_928_;
goto _start;
}
}
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_934_, lean_object* v_k_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_934_, v_k_935_);
lean_dec(v_k_935_);
lean_dec(v_t_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_937_, lean_object* v_self_938_){
_start:
{
lean_object* v_targetDeclMap_939_; lean_object* v___x_940_; 
v_targetDeclMap_939_ = lean_ctor_get(v_self_938_, 15);
v___x_940_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_939_, v_name_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_941_, lean_object* v_self_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lake_Package_findTargetDecl_x3f(v_name_941_, v_self_942_);
lean_dec_ref(v_self_942_);
lean_dec(v_name_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_944_, lean_object* v_inst_945_, lean_object* v_t_946_, lean_object* v_k_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_946_, v_k_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_949_, lean_object* v_inst_950_, lean_object* v_t_951_, lean_object* v_k_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_949_, v_inst_950_, v_t_951_, v_k_952_);
lean_dec(v_k_952_);
lean_dec(v_t_951_);
return v_res_953_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_957_, lean_object* v_as_958_, size_t v_i_959_, size_t v_stop_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_eq(v_i_959_, v_stop_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v_kind_963_; lean_object* v_config_964_; uint8_t v___x_965_; uint8_t v___y_967_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_962_ = lean_array_uget_borrowed(v_as_958_, v_i_959_);
v_kind_963_ = lean_ctor_get(v___x_962_, 2);
v_config_964_ = lean_ctor_get(v___x_962_, 3);
v___x_965_ = 1;
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_972_ = lean_name_eq(v_kind_963_, v___x_971_);
if (v___x_972_ == 0)
{
v___y_967_ = v___x_961_;
goto v___jp_966_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_957_, v_config_964_);
v___y_967_ = v___x_973_;
goto v___jp_966_;
}
v___jp_966_:
{
if (v___y_967_ == 0)
{
size_t v___x_968_; size_t v___x_969_; 
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_i_959_, v___x_968_);
v_i_959_ = v___x_969_;
goto _start;
}
else
{
return v___x_965_;
}
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_975_, lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_){
_start:
{
size_t v_i_boxed_979_; size_t v_stop_boxed_980_; uint8_t v_res_981_; lean_object* v_r_982_; 
v_i_boxed_979_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_980_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_975_, v_as_976_, v_i_boxed_979_, v_stop_boxed_980_);
lean_dec_ref(v_as_976_);
lean_dec(v_mod_975_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_983_, lean_object* v_self_984_){
_start:
{
lean_object* v_targetDecls_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_targetDecls_985_ = lean_ctor_get(v_self_984_, 14);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_targetDecls_985_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
return v___x_988_;
}
else
{
if (v___x_988_ == 0)
{
return v___x_988_;
}
else
{
size_t v___x_989_; size_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_987_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_983_, v_targetDecls_985_, v___x_989_, v___x_990_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_992_, lean_object* v_self_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Lake_Package_isLocalModule(v_mod_992_, v_self_993_);
lean_dec_ref(v_self_993_);
lean_dec(v_mod_992_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_996_, lean_object* v_as_997_, size_t v_i_998_, size_t v_stop_999_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_eq(v_i_998_, v_stop_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v_kind_1002_; lean_object* v_config_1003_; uint8_t v___x_1004_; uint8_t v___y_1006_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1001_ = lean_array_uget_borrowed(v_as_997_, v_i_998_);
v_kind_1002_ = lean_ctor_get(v___x_1001_, 2);
v_config_1003_ = lean_ctor_get(v___x_1001_, 3);
v___x_1004_ = 1;
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1018_ = lean_name_eq(v_kind_1002_, v___x_1017_);
if (v___x_1018_ == 0)
{
goto v___jp_1010_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_996_, v_config_1003_);
if (v___x_1019_ == 0)
{
goto v___jp_1010_;
}
else
{
v___y_1006_ = v___x_1019_;
goto v___jp_1005_;
}
}
v___jp_1005_:
{
if (v___y_1006_ == 0)
{
size_t v___x_1007_; size_t v___x_1008_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_998_, v___x_1007_);
v_i_998_ = v___x_1008_;
goto _start;
}
else
{
return v___x_1004_;
}
}
v___jp_1010_:
{
lean_object* v_kind_1011_; lean_object* v_config_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_kind_1011_ = lean_ctor_get(v___x_1001_, 2);
v_config_1012_ = lean_ctor_get(v___x_1001_, 3);
v___x_1013_ = l_Lake_LeanExe_keyword;
v___x_1014_ = lean_name_eq(v_kind_1011_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_1006_ = v___x_1000_;
goto v___jp_1005_;
}
else
{
lean_object* v_root_1015_; uint8_t v___x_1016_; 
v_root_1015_ = lean_ctor_get(v_config_1012_, 2);
v___x_1016_ = lean_name_eq(v_root_1015_, v_mod_996_);
v___y_1006_ = v___x_1016_;
goto v___jp_1005_;
}
}
}
else
{
uint8_t v___x_1020_; 
v___x_1020_ = 0;
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1021_, lean_object* v_as_1022_, lean_object* v_i_1023_, lean_object* v_stop_1024_){
_start:
{
size_t v_i_boxed_1025_; size_t v_stop_boxed_1026_; uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_i_boxed_1025_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1024_);
lean_dec(v_stop_1024_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1021_, v_as_1022_, v_i_boxed_1025_, v_stop_boxed_1026_);
lean_dec_ref(v_as_1022_);
lean_dec(v_mod_1021_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1029_, lean_object* v_self_1030_){
_start:
{
lean_object* v_targetDecls_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_targetDecls_1031_ = lean_ctor_get(v_self_1030_, 14);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_array_get_size(v_targetDecls_1031_);
v___x_1034_ = lean_nat_dec_lt(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
return v___x_1034_;
}
else
{
if (v___x_1034_ == 0)
{
return v___x_1034_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1033_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1029_, v_targetDecls_1031_, v___x_1035_, v___x_1036_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1038_, lean_object* v_self_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Lake_Package_isBuildableModule(v_mod_1038_, v_self_1039_);
lean_dec_ref(v_self_1039_);
lean_dec(v_mod_1038_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1042_){
_start:
{
lean_object* v_config_1044_; lean_object* v_dir_1045_; lean_object* v_buildDir_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_config_1044_ = lean_ctor_get(v_self_1042_, 6);
lean_inc_ref(v_config_1044_);
v_dir_1045_ = lean_ctor_get(v_self_1042_, 4);
lean_inc_ref(v_dir_1045_);
lean_dec_ref(v_self_1042_);
v_buildDir_1046_ = lean_ctor_get(v_config_1044_, 5);
lean_inc_ref(v_buildDir_1046_);
lean_dec_ref(v_config_1044_);
v___x_1047_ = l_System_FilePath_normalize(v_buildDir_1046_);
v___x_1048_ = l_Lake_joinRelative(v_dir_1045_, v___x_1047_);
v___x_1049_ = l_Lake_removeDirAllIfExists(v___x_1048_);
lean_dec_ref(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lake_Package_clean(v_self_1050_);
return v_res_1052_;
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
