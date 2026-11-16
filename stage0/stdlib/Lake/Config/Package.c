// Lean compiler output
// Module: Lake.Config.Package
// Imports: public import Lake.Config.Cache public import Lake.Config.Script public import Lake.Config.ConfigDecl public import Lake.Config.Dependency public import Lake.Config.PackageConfig public import Lake.Config.LakeConfig public import Lake.Util.FilePath public import Lake.Util.OrdHashSet public import Lake.Util.Name meta import all Lake.Util.OpaqueType import Lake.Util.OpaqueType import Lake.Util.IO
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lake_LeanExe_keyword;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_CacheToolchain_none;
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_CachePlatform_none;
lean_object* l_Lake_instInhabitedPackageConfig_default___redArg();
lean_object* l_Lake_OrdHashSet_empty___redArg();
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_removeDirAllIfExists(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg();
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg___boxed(lean_object*);
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
static size_t l_Lake_instInhabitedPackage_default___closed__12;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__13;
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
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_NPackage_instCoeOutPackage___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___closed__0 = (const lean_object*)&l_Lake_NPackage_instCoeOutPackage___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg();
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0 = (const lean_object*)&l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg();
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Package_downloadCacheService_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_precompileImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_precompileImports___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Internal_cacheToolchain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_cacheToolchain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_cachePlatform(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_cachePlatform___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object* v_pkg_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object* v_pkg_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(v_pkg_7_);
lean_dec(v_pkg_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(lean_object* v_k_9_, lean_object* v_v_10_, lean_object* v_t_11_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_size_12_; lean_object* v_k_13_; lean_object* v_v_14_; lean_object* v_l_15_; lean_object* v_r_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_296_; 
v_size_12_ = lean_ctor_get(v_t_11_, 0);
v_k_13_ = lean_ctor_get(v_t_11_, 1);
v_v_14_ = lean_ctor_get(v_t_11_, 2);
v_l_15_ = lean_ctor_get(v_t_11_, 3);
v_r_16_ = lean_ctor_get(v_t_11_, 4);
v_isSharedCheck_296_ = !lean_is_exclusive(v_t_11_);
if (v_isSharedCheck_296_ == 0)
{
v___x_18_ = v_t_11_;
v_isShared_19_ = v_isSharedCheck_296_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_r_16_);
lean_inc(v_l_15_);
lean_inc(v_v_14_);
lean_inc(v_k_13_);
lean_inc(v_size_12_);
lean_dec(v_t_11_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_296_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; 
v___x_20_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_9_, v_k_13_);
switch(v___x_20_)
{
case 0:
{
lean_object* v_impl_21_; lean_object* v___x_22_; 
lean_dec(v_size_12_);
v_impl_21_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_9_, v_v_10_, v_l_15_);
v___x_22_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_16_) == 0)
{
lean_object* v_size_23_; lean_object* v_size_24_; lean_object* v_k_25_; lean_object* v_v_26_; lean_object* v_l_27_; lean_object* v_r_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_size_23_ = lean_ctor_get(v_r_16_, 0);
v_size_24_ = lean_ctor_get(v_impl_21_, 0);
v_k_25_ = lean_ctor_get(v_impl_21_, 1);
v_v_26_ = lean_ctor_get(v_impl_21_, 2);
v_l_27_ = lean_ctor_get(v_impl_21_, 3);
v_r_28_ = lean_ctor_get(v_impl_21_, 4);
lean_inc(v_r_28_);
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_nat_mul(v___x_29_, v_size_23_);
v___x_31_ = lean_nat_dec_lt(v___x_30_, v_size_24_);
lean_dec(v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
lean_dec(v_r_28_);
v___x_32_ = lean_nat_add(v___x_22_, v_size_24_);
v___x_33_ = lean_nat_add(v___x_32_, v_size_23_);
lean_dec(v___x_32_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 3, v_impl_21_);
lean_ctor_set(v___x_18_, 0, v___x_33_);
v___x_35_ = v___x_18_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_36_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_36_, 3, v_impl_21_);
lean_ctor_set(v_reuseFailAlloc_36_, 4, v_r_16_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
else
{
lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_102_; 
lean_inc(v_l_27_);
lean_inc(v_v_26_);
lean_inc(v_k_25_);
lean_inc(v_size_24_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_impl_21_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; lean_object* v_unused_106_; lean_object* v_unused_107_; 
v_unused_103_ = lean_ctor_get(v_impl_21_, 4);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_impl_21_, 3);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_impl_21_, 2);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_impl_21_, 1);
lean_dec(v_unused_106_);
v_unused_107_ = lean_ctor_get(v_impl_21_, 0);
lean_dec(v_unused_107_);
v___x_38_ = v_impl_21_;
v_isShared_39_ = v_isSharedCheck_102_;
goto v_resetjp_37_;
}
else
{
lean_dec(v_impl_21_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_102_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_size_40_; lean_object* v_size_41_; lean_object* v_k_42_; lean_object* v_v_43_; lean_object* v_l_44_; lean_object* v_r_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_size_40_ = lean_ctor_get(v_l_27_, 0);
v_size_41_ = lean_ctor_get(v_r_28_, 0);
v_k_42_ = lean_ctor_get(v_r_28_, 1);
v_v_43_ = lean_ctor_get(v_r_28_, 2);
v_l_44_ = lean_ctor_get(v_r_28_, 3);
v_r_45_ = lean_ctor_get(v_r_28_, 4);
v___x_46_ = lean_unsigned_to_nat(2u);
v___x_47_ = lean_nat_mul(v___x_46_, v_size_40_);
v___x_48_ = lean_nat_dec_lt(v_size_41_, v___x_47_);
lean_dec(v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_77_; 
lean_inc(v_r_45_);
lean_inc(v_l_44_);
lean_inc(v_v_43_);
lean_inc(v_k_42_);
v_isSharedCheck_77_ = !lean_is_exclusive(v_r_28_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; lean_object* v_unused_79_; lean_object* v_unused_80_; lean_object* v_unused_81_; lean_object* v_unused_82_; 
v_unused_78_ = lean_ctor_get(v_r_28_, 4);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_r_28_, 3);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v_r_28_, 2);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_r_28_, 1);
lean_dec(v_unused_81_);
v_unused_82_ = lean_ctor_get(v_r_28_, 0);
lean_dec(v_unused_82_);
v___x_50_ = v_r_28_;
v_isShared_51_ = v_isSharedCheck_77_;
goto v_resetjp_49_;
}
else
{
lean_dec(v_r_28_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_77_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___x_65_; lean_object* v___y_67_; 
v___x_52_ = lean_nat_add(v___x_22_, v_size_24_);
lean_dec(v_size_24_);
v___x_53_ = lean_nat_add(v___x_52_, v_size_23_);
lean_dec(v___x_52_);
v___x_65_ = lean_nat_add(v___x_22_, v_size_40_);
if (lean_obj_tag(v_l_44_) == 0)
{
lean_object* v_size_75_; 
v_size_75_ = lean_ctor_get(v_l_44_, 0);
lean_inc(v_size_75_);
v___y_67_ = v_size_75_;
goto v___jp_66_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___y_67_ = v___x_76_;
goto v___jp_66_;
}
v___jp_54_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_nat_add(v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 4, v_r_16_);
lean_ctor_set(v___x_50_, 3, v_r_45_);
lean_ctor_set(v___x_50_, 2, v_v_14_);
lean_ctor_set(v___x_50_, 1, v_k_13_);
lean_ctor_set(v___x_50_, 0, v___x_58_);
v___x_60_ = v___x_50_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_r_45_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_r_16_);
v___x_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_62_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 4, v___x_60_);
lean_ctor_set(v___x_38_, 3, v___y_55_);
lean_ctor_set(v___x_38_, 2, v_v_43_);
lean_ctor_set(v___x_38_, 1, v_k_42_);
lean_ctor_set(v___x_38_, 0, v___x_53_);
v___x_62_ = v___x_38_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_k_42_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_v_43_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v___y_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_nat_add(v___x_65_, v___y_67_);
lean_dec(v___y_67_);
lean_dec(v___x_65_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_l_44_);
lean_ctor_set(v___x_18_, 3, v_l_27_);
lean_ctor_set(v___x_18_, 2, v_v_26_);
lean_ctor_set(v___x_18_, 1, v_k_25_);
lean_ctor_set(v___x_18_, 0, v___x_68_);
v___x_70_ = v___x_18_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v_l_44_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_nat_add(v___x_22_, v_size_23_);
if (lean_obj_tag(v_r_45_) == 0)
{
lean_object* v_size_72_; 
v_size_72_ = lean_ctor_get(v_r_45_, 0);
lean_inc(v_size_72_);
v___y_55_ = v___x_70_;
v___y_56_ = v___x_71_;
v___y_57_ = v_size_72_;
goto v___jp_54_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___y_55_ = v___x_70_;
v___y_56_ = v___x_71_;
v___y_57_ = v___x_73_;
goto v___jp_54_;
}
}
}
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
lean_del_object(v___x_18_);
v___x_83_ = lean_nat_add(v___x_22_, v_size_24_);
lean_dec(v_size_24_);
v___x_84_ = lean_nat_add(v___x_83_, v_size_23_);
lean_dec(v___x_83_);
v___x_85_ = lean_nat_add(v___x_22_, v_size_23_);
v___x_86_ = lean_nat_add(v___x_85_, v_size_41_);
lean_dec(v___x_85_);
lean_inc_ref(v_r_16_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 4, v_r_16_);
lean_ctor_set(v___x_38_, 3, v_r_28_);
lean_ctor_set(v___x_38_, 2, v_v_14_);
lean_ctor_set(v___x_38_, 1, v_k_13_);
lean_ctor_set(v___x_38_, 0, v___x_86_);
v___x_88_ = v___x_38_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_r_28_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v_r_16_);
v___x_88_ = v_reuseFailAlloc_101_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_isSharedCheck_95_ = !lean_is_exclusive(v_r_16_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; lean_object* v_unused_100_; 
v_unused_96_ = lean_ctor_get(v_r_16_, 4);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_r_16_, 3);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_r_16_, 2);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_r_16_, 1);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v_r_16_, 0);
lean_dec(v_unused_100_);
v___x_90_ = v_r_16_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_r_16_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 4, v___x_88_);
lean_ctor_set(v___x_90_, 3, v_l_27_);
lean_ctor_set(v___x_90_, 2, v_v_26_);
lean_ctor_set(v___x_90_, 1, v_k_25_);
lean_ctor_set(v___x_90_, 0, v___x_84_);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v___x_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_108_; 
v_l_108_ = lean_ctor_get(v_impl_21_, 3);
if (lean_obj_tag(v_l_108_) == 0)
{
lean_object* v_r_109_; lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
lean_inc_ref(v_l_108_);
v_r_109_ = lean_ctor_get(v_impl_21_, 4);
v_k_110_ = lean_ctor_get(v_impl_21_, 1);
v_v_111_ = lean_ctor_get(v_impl_21_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_impl_21_);
if (v_isSharedCheck_122_ == 0)
{
lean_object* v_unused_123_; lean_object* v_unused_124_; 
v_unused_123_ = lean_ctor_get(v_impl_21_, 3);
lean_dec(v_unused_123_);
v_unused_124_ = lean_ctor_get(v_impl_21_, 0);
lean_dec(v_unused_124_);
v___x_113_ = v_impl_21_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_r_109_);
lean_inc(v_v_111_);
lean_inc(v_k_110_);
lean_dec(v_impl_21_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 3, v_r_109_);
lean_ctor_set(v___x_113_, 2, v_v_14_);
lean_ctor_set(v___x_113_, 1, v_k_13_);
lean_ctor_set(v___x_113_, 0, v___x_22_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_r_109_);
lean_ctor_set(v_reuseFailAlloc_121_, 4, v_r_109_);
v___x_117_ = v_reuseFailAlloc_121_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_117_);
lean_ctor_set(v___x_18_, 3, v_l_108_);
lean_ctor_set(v___x_18_, 2, v_v_111_);
lean_ctor_set(v___x_18_, 1, v_k_110_);
lean_ctor_set(v___x_18_, 0, v___x_115_);
v___x_119_ = v___x_18_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_120_, 4, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
else
{
lean_object* v_r_125_; 
v_r_125_ = lean_ctor_get(v_impl_21_, 4);
lean_inc(v_r_125_);
if (lean_obj_tag(v_r_125_) == 0)
{
lean_object* v_k_126_; lean_object* v_v_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_150_; 
lean_inc(v_l_108_);
v_k_126_ = lean_ctor_get(v_impl_21_, 1);
v_v_127_ = lean_ctor_get(v_impl_21_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v_impl_21_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; 
v_unused_151_ = lean_ctor_get(v_impl_21_, 4);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_impl_21_, 3);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_impl_21_, 0);
lean_dec(v_unused_153_);
v___x_129_ = v_impl_21_;
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_v_127_);
lean_inc(v_k_126_);
lean_dec(v_impl_21_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_k_131_; lean_object* v_v_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_146_; 
v_k_131_ = lean_ctor_get(v_r_125_, 1);
v_v_132_ = lean_ctor_get(v_r_125_, 2);
v_isSharedCheck_146_ = !lean_is_exclusive(v_r_125_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; lean_object* v_unused_148_; lean_object* v_unused_149_; 
v_unused_147_ = lean_ctor_get(v_r_125_, 4);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_r_125_, 3);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_r_125_, 0);
lean_dec(v_unused_149_);
v___x_134_ = v_r_125_;
v_isShared_135_ = v_isSharedCheck_146_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_v_132_);
lean_inc(v_k_131_);
lean_dec(v_r_125_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_146_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(3u);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 4, v_l_108_);
lean_ctor_set(v___x_134_, 3, v_l_108_);
lean_ctor_set(v___x_134_, 2, v_v_127_);
lean_ctor_set(v___x_134_, 1, v_k_126_);
lean_ctor_set(v___x_134_, 0, v___x_22_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_l_108_);
v___x_138_ = v_reuseFailAlloc_145_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_108_);
lean_ctor_set(v___x_129_, 2, v_v_14_);
lean_ctor_set(v___x_129_, 1, v_k_13_);
lean_ctor_set(v___x_129_, 0, v___x_22_);
v___x_140_ = v___x_129_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_l_108_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_140_);
lean_ctor_set(v___x_18_, 3, v___x_138_);
lean_ctor_set(v___x_18_, 2, v_v_132_);
lean_ctor_set(v___x_18_, 1, v_k_131_);
lean_ctor_set(v___x_18_, 0, v___x_136_);
v___x_142_ = v___x_18_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_131_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_132_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(2u);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_r_125_);
lean_ctor_set(v___x_18_, 3, v_impl_21_);
lean_ctor_set(v___x_18_, 0, v___x_154_);
v___x_156_ = v___x_18_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_impl_21_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_r_125_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
case 1:
{
lean_object* v___x_159_; 
lean_dec(v_v_14_);
lean_dec(v_k_13_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v_v_10_);
lean_ctor_set(v___x_18_, 1, v_k_9_);
v___x_159_ = v___x_18_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_12_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_r_16_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
default: 
{
lean_object* v_impl_161_; lean_object* v___x_162_; 
lean_dec(v_size_12_);
v_impl_161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_9_, v_v_10_, v_r_16_);
v___x_162_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_15_) == 0)
{
lean_object* v_size_163_; lean_object* v_size_164_; lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v_l_167_; lean_object* v_r_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_size_163_ = lean_ctor_get(v_l_15_, 0);
v_size_164_ = lean_ctor_get(v_impl_161_, 0);
v_k_165_ = lean_ctor_get(v_impl_161_, 1);
v_v_166_ = lean_ctor_get(v_impl_161_, 2);
v_l_167_ = lean_ctor_get(v_impl_161_, 3);
lean_inc(v_l_167_);
v_r_168_ = lean_ctor_get(v_impl_161_, 4);
v___x_169_ = lean_unsigned_to_nat(3u);
v___x_170_ = lean_nat_mul(v___x_169_, v_size_163_);
v___x_171_ = lean_nat_dec_lt(v___x_170_, v_size_164_);
lean_dec(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec(v_l_167_);
v___x_172_ = lean_nat_add(v___x_162_, v_size_163_);
v___x_173_ = lean_nat_add(v___x_172_, v_size_164_);
lean_dec(v___x_172_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_impl_161_);
lean_ctor_set(v___x_18_, 0, v___x_173_);
v___x_175_ = v___x_18_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_impl_161_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
else
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_240_; 
lean_inc(v_r_168_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
lean_inc(v_size_164_);
v_isSharedCheck_240_ = !lean_is_exclusive(v_impl_161_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_241_ = lean_ctor_get(v_impl_161_, 4);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_impl_161_, 3);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_impl_161_, 2);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_impl_161_, 1);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_impl_161_, 0);
lean_dec(v_unused_245_);
v___x_178_ = v_impl_161_;
v_isShared_179_ = v_isSharedCheck_240_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_impl_161_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_240_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_size_180_; lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v_l_183_; lean_object* v_r_184_; lean_object* v_size_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_size_180_ = lean_ctor_get(v_l_167_, 0);
v_k_181_ = lean_ctor_get(v_l_167_, 1);
v_v_182_ = lean_ctor_get(v_l_167_, 2);
v_l_183_ = lean_ctor_get(v_l_167_, 3);
v_r_184_ = lean_ctor_get(v_l_167_, 4);
v_size_185_ = lean_ctor_get(v_r_168_, 0);
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = lean_nat_mul(v___x_186_, v_size_185_);
v___x_188_ = lean_nat_dec_lt(v_size_180_, v___x_187_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_216_; 
lean_inc(v_r_184_);
lean_inc(v_l_183_);
lean_inc(v_v_182_);
lean_inc(v_k_181_);
v_isSharedCheck_216_ = !lean_is_exclusive(v_l_167_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_217_ = lean_ctor_get(v_l_167_, 4);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_l_167_, 3);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_l_167_, 2);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_l_167_, 1);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_l_167_, 0);
lean_dec(v_unused_221_);
v___x_190_ = v_l_167_;
v_isShared_191_ = v_isSharedCheck_216_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_l_167_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_216_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_206_; 
v___x_192_ = lean_nat_add(v___x_162_, v_size_163_);
v___x_193_ = lean_nat_add(v___x_192_, v_size_164_);
lean_dec(v_size_164_);
if (lean_obj_tag(v_l_183_) == 0)
{
lean_object* v_size_214_; 
v_size_214_ = lean_ctor_get(v_l_183_, 0);
lean_inc(v_size_214_);
v___y_206_ = v_size_214_;
goto v___jp_205_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___y_206_ = v___x_215_;
goto v___jp_205_;
}
v___jp_194_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_nat_add(v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec(v___y_196_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v_r_168_);
lean_ctor_set(v___x_190_, 3, v_r_184_);
lean_ctor_set(v___x_190_, 2, v_v_166_);
lean_ctor_set(v___x_190_, 1, v_k_165_);
lean_ctor_set(v___x_190_, 0, v___x_198_);
v___x_200_ = v___x_190_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_r_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_r_168_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_200_);
lean_ctor_set(v___x_178_, 3, v___y_195_);
lean_ctor_set(v___x_178_, 2, v_v_182_);
lean_ctor_set(v___x_178_, 1, v_k_181_);
lean_ctor_set(v___x_178_, 0, v___x_193_);
v___x_202_ = v___x_178_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_181_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_182_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___y_195_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_nat_add(v___x_192_, v___y_206_);
lean_dec(v___y_206_);
lean_dec(v___x_192_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_l_183_);
lean_ctor_set(v___x_18_, 0, v___x_207_);
v___x_209_ = v___x_18_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_l_183_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_nat_add(v___x_162_, v_size_185_);
if (lean_obj_tag(v_r_184_) == 0)
{
lean_object* v_size_211_; 
v_size_211_ = lean_ctor_get(v_r_184_, 0);
lean_inc(v_size_211_);
v___y_195_ = v___x_209_;
v___y_196_ = v___x_210_;
v___y_197_ = v_size_211_;
goto v___jp_194_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___y_195_ = v___x_209_;
v___y_196_ = v___x_210_;
v___y_197_ = v___x_212_;
goto v___jp_194_;
}
}
}
}
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
lean_del_object(v___x_18_);
v___x_222_ = lean_nat_add(v___x_162_, v_size_163_);
v___x_223_ = lean_nat_add(v___x_222_, v_size_164_);
lean_dec(v_size_164_);
v___x_224_ = lean_nat_add(v___x_222_, v_size_180_);
lean_dec(v___x_222_);
lean_inc_ref(v_l_15_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_l_167_);
lean_ctor_set(v___x_178_, 3, v_l_15_);
lean_ctor_set(v___x_178_, 2, v_v_14_);
lean_ctor_set(v___x_178_, 1, v_k_13_);
lean_ctor_set(v___x_178_, 0, v___x_224_);
v___x_226_ = v___x_178_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_l_167_);
v___x_226_ = v_reuseFailAlloc_239_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_isSharedCheck_233_ = !lean_is_exclusive(v_l_15_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_234_ = lean_ctor_get(v_l_15_, 4);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_l_15_, 3);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_l_15_, 2);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_l_15_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_l_15_, 0);
lean_dec(v_unused_238_);
v___x_228_ = v_l_15_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_dec(v_l_15_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 4, v_r_168_);
lean_ctor_set(v___x_228_, 3, v___x_226_);
lean_ctor_set(v___x_228_, 2, v_v_166_);
lean_ctor_set(v___x_228_, 1, v_k_165_);
lean_ctor_set(v___x_228_, 0, v___x_223_);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_r_168_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_246_; 
v_l_246_ = lean_ctor_get(v_impl_161_, 3);
lean_inc(v_l_246_);
if (lean_obj_tag(v_l_246_) == 0)
{
lean_object* v_r_247_; lean_object* v_k_248_; lean_object* v_v_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_272_; 
v_r_247_ = lean_ctor_get(v_impl_161_, 4);
v_k_248_ = lean_ctor_get(v_impl_161_, 1);
v_v_249_ = lean_ctor_get(v_impl_161_, 2);
v_isSharedCheck_272_ = !lean_is_exclusive(v_impl_161_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; lean_object* v_unused_274_; 
v_unused_273_ = lean_ctor_get(v_impl_161_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_impl_161_, 0);
lean_dec(v_unused_274_);
v___x_251_ = v_impl_161_;
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_r_247_);
lean_inc(v_v_249_);
lean_inc(v_k_248_);
lean_dec(v_impl_161_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_k_253_; lean_object* v_v_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_268_; 
v_k_253_ = lean_ctor_get(v_l_246_, 1);
v_v_254_ = lean_ctor_get(v_l_246_, 2);
v_isSharedCheck_268_ = !lean_is_exclusive(v_l_246_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_269_ = lean_ctor_get(v_l_246_, 4);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_l_246_, 3);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_l_246_, 0);
lean_dec(v_unused_271_);
v___x_256_ = v_l_246_;
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_v_254_);
lean_inc(v_k_253_);
lean_dec(v_l_246_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_247_, 2);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v_r_247_);
lean_ctor_set(v___x_256_, 3, v_r_247_);
lean_ctor_set(v___x_256_, 2, v_v_14_);
lean_ctor_set(v___x_256_, 1, v_k_13_);
lean_ctor_set(v___x_256_, 0, v___x_162_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_r_247_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_r_247_);
v___x_260_ = v_reuseFailAlloc_267_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
lean_inc(v_r_247_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 3, v_r_247_);
lean_ctor_set(v___x_251_, 0, v___x_162_);
v___x_262_ = v___x_251_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_k_248_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_v_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_r_247_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_r_247_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_262_);
lean_ctor_set(v___x_18_, 3, v___x_260_);
lean_ctor_set(v___x_18_, 2, v_v_254_);
lean_ctor_set(v___x_18_, 1, v_k_253_);
lean_ctor_set(v___x_18_, 0, v___x_258_);
v___x_264_ = v___x_18_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_k_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_v_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
else
{
lean_object* v_r_275_; 
v_r_275_ = lean_ctor_get(v_impl_161_, 4);
lean_inc(v_r_275_);
if (lean_obj_tag(v_r_275_) == 0)
{
lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_288_; 
v_k_276_ = lean_ctor_get(v_impl_161_, 1);
v_v_277_ = lean_ctor_get(v_impl_161_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_impl_161_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_289_ = lean_ctor_get(v_impl_161_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_impl_161_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_impl_161_, 0);
lean_dec(v_unused_291_);
v___x_279_ = v_impl_161_;
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_v_277_);
lean_inc(v_k_276_);
lean_dec(v_impl_161_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(3u);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 4, v_l_246_);
lean_ctor_set(v___x_279_, 2, v_v_14_);
lean_ctor_set(v___x_279_, 1, v_k_13_);
lean_ctor_set(v___x_279_, 0, v___x_162_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_246_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_l_246_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_r_275_);
lean_ctor_set(v___x_18_, 3, v___x_283_);
lean_ctor_set(v___x_18_, 2, v_v_277_);
lean_ctor_set(v___x_18_, 1, v_k_276_);
lean_ctor_set(v___x_18_, 0, v___x_281_);
v___x_285_ = v___x_18_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_r_275_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(2u);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_impl_161_);
lean_ctor_set(v___x_18_, 3, v_r_275_);
lean_ctor_set(v___x_18_, 0, v___x_292_);
v___x_294_ = v___x_18_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_r_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_impl_161_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
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
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_k_9_);
lean_ctor_set(v___x_298_, 2, v_v_10_);
lean_ctor_set(v___x_298_, 3, v_t_11_);
lean_ctor_set(v___x_298_, 4, v_t_11_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(lean_object* v_as_299_, size_t v_i_300_, size_t v_stop_301_, lean_object* v_b_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = lean_usize_dec_eq(v_i_300_, v_stop_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v_name_305_; lean_object* v___x_306_; size_t v___x_307_; size_t v___x_308_; 
v___x_304_ = lean_array_uget_borrowed(v_as_299_, v_i_300_);
v_name_305_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v___x_304_);
lean_inc(v_name_305_);
v___x_306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_name_305_, v___x_304_, v_b_302_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_300_, v___x_307_);
v_i_300_ = v___x_308_;
v_b_302_ = v___x_306_;
goto _start;
}
else
{
return v_b_302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1___boxed(lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_, lean_object* v_b_313_){
_start:
{
size_t v_i_boxed_314_; size_t v_stop_boxed_315_; lean_object* v_res_316_; 
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_315_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v_as_310_, v_i_boxed_314_, v_stop_boxed_315_, v_b_313_);
lean_dec_ref(v_as_310_);
return v_res_316_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__2(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v___x_321_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__4(void){
_start:
{
uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = 0;
v___x_325_ = lean_box(0);
v___x_326_ = l_Lean_Name_toString(v___x_325_, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__6(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__5));
v___x_329_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__4, &l_Lake_instInhabitedPackage_default___closed__4_once, _init_l_Lake_instInhabitedPackage_default___closed__4);
v___x_330_ = lean_string_append(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_System_Platform_target;
v___x_332_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__6, &l_Lake_instInhabitedPackage_default___closed__6_once, _init_l_Lake_instInhabitedPackage_default___closed__6);
v___x_333_ = lean_string_append(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__9(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__8));
v___x_336_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__7, &l_Lake_instInhabitedPackage_default___closed__7_once, _init_l_Lake_instInhabitedPackage_default___closed__7);
v___x_337_ = lean_string_append(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__10(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_339_ = lean_array_get_size(v___x_338_);
return v___x_339_;
}
}
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__11(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_nat_dec_lt(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static size_t _init_l_Lake_instInhabitedPackage_default___closed__12(void){
_start:
{
lean_object* v___x_343_; size_t v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_344_ = lean_usize_of_nat(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__13(void){
_start:
{
lean_object* v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = lean_box(1);
v___x_346_ = lean_usize_once(&l_Lake_instInhabitedPackage_default___closed__12, &l_Lake_instInhabitedPackage_default___closed__12_once, _init_l_Lake_instInhabitedPackage_default___closed__12);
v___x_347_ = ((size_t)0ULL);
v___x_348_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v___x_348_, v___x_347_, v___x_346_, v___x_345_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_368_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_box(0);
v___x_352_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_353_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_354_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__2, &l_Lake_instInhabitedPackage_default___closed__2_once, _init_l_Lake_instInhabitedPackage_default___closed__2);
v___x_355_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_373_ = lean_box(1);
v___x_374_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__11, &l_Lake_instInhabitedPackage_default___closed__11_once, _init_l_Lake_instInhabitedPackage_default___closed__11);
if (v___x_374_ == 0)
{
v___y_368_ = v___x_373_;
goto v___jp_367_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__13, &l_Lake_instInhabitedPackage_default___closed__13_once, _init_l_Lake_instInhabitedPackage_default___closed__13);
v___y_368_ = v___x_375_;
goto v___jp_367_;
}
v___jp_356_:
{
lean_object* v_testDriver_364_; lean_object* v_lintDriver_365_; lean_object* v___x_366_; 
v_testDriver_364_ = lean_ctor_get(v___x_354_, 13);
v_lintDriver_365_ = lean_ctor_get(v___x_354_, 15);
lean_inc_ref(v_lintDriver_365_);
lean_inc_ref(v_testDriver_364_);
lean_inc_ref(v___y_363_);
lean_inc_ref(v___y_360_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_361_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_362_);
lean_inc(v___y_359_);
v___x_366_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v___x_366_, 0, v___x_350_);
lean_ctor_set(v___x_366_, 1, v___x_351_);
lean_ctor_set(v___x_366_, 2, v___x_352_);
lean_ctor_set(v___x_366_, 3, v___x_351_);
lean_ctor_set(v___x_366_, 4, v___x_353_);
lean_ctor_set(v___x_366_, 5, v___x_353_);
lean_ctor_set(v___x_366_, 6, v___x_354_);
lean_ctor_set(v___x_366_, 7, v___x_353_);
lean_ctor_set(v___x_366_, 8, v___x_353_);
lean_ctor_set(v___x_366_, 9, v___x_353_);
lean_ctor_set(v___x_366_, 10, v___x_353_);
lean_ctor_set(v___x_366_, 11, v___x_353_);
lean_ctor_set(v___x_366_, 12, v___x_355_);
lean_ctor_set(v___x_366_, 13, v___x_355_);
lean_ctor_set(v___x_366_, 14, v___x_355_);
lean_ctor_set(v___x_366_, 15, v___x_355_);
lean_ctor_set(v___x_366_, 16, v___y_359_);
lean_ctor_set(v___x_366_, 17, v___y_362_);
lean_ctor_set(v___x_366_, 18, v___y_358_);
lean_ctor_set(v___x_366_, 19, v___y_361_);
lean_ctor_set(v___x_366_, 20, v___y_357_);
lean_ctor_set(v___x_366_, 21, v___y_360_);
lean_ctor_set(v___x_366_, 22, v___y_363_);
lean_ctor_set(v___x_366_, 23, v_testDriver_364_);
lean_ctor_set(v___x_366_, 24, v_lintDriver_365_);
return v___x_366_;
}
v___jp_367_:
{
lean_object* v_buildArchive_369_; lean_object* v___x_370_; 
v_buildArchive_369_ = lean_ctor_get(v___x_354_, 11);
v___x_370_ = lean_box(1);
if (lean_obj_tag(v_buildArchive_369_) == 1)
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v_buildArchive_369_, 0);
v___y_357_ = v___x_355_;
v___y_358_ = v___x_370_;
v___y_359_ = v___y_368_;
v___y_360_ = v___x_355_;
v___y_361_ = v___x_370_;
v___y_362_ = v___x_355_;
v___y_363_ = v_val_371_;
goto v___jp_356_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__9, &l_Lake_instInhabitedPackage_default___closed__9_once, _init_l_Lake_instInhabitedPackage_default___closed__9);
v___y_357_ = v___x_355_;
v___y_358_ = v___x_370_;
v___y_359_ = v___y_368_;
v___y_360_ = v___x_355_;
v___y_361_ = v___x_370_;
v___y_362_ = v___x_355_;
v___y_363_ = v___x_372_;
goto v___jp_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object* v_00_u03b2_376_, lean_object* v_k_377_, lean_object* v_v_378_, lean_object* v_t_379_, lean_object* v_hl_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_377_, v_v_378_, v_t_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lake_instInhabitedPackage_default;
return v___x_382_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_383_){
_start:
{
lean_object* v_keyName_384_; 
v_keyName_384_ = lean_ctor_get(v_pkg_383_, 2);
if (lean_obj_tag(v_keyName_384_) == 0)
{
uint64_t v___x_385_; 
v___x_385_ = 1723ULL;
return v___x_385_;
}
else
{
uint64_t v_hash_386_; 
v_hash_386_ = lean_ctor_get_uint64(v_keyName_384_, sizeof(void*)*2);
return v_hash_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_387_){
_start:
{
uint64_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lake_Package_instHashable___lam__0(v_pkg_387_);
lean_dec_ref(v_pkg_387_);
v_r_389_ = lean_box_uint64(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_392_, lean_object* v_p2_393_){
_start:
{
lean_object* v_wsIdx_394_; lean_object* v_wsIdx_395_; uint8_t v___x_396_; 
v_wsIdx_394_ = lean_ctor_get(v_p1_392_, 0);
v_wsIdx_395_ = lean_ctor_get(v_p2_393_, 0);
v___x_396_ = lean_nat_dec_eq(v_wsIdx_394_, v_wsIdx_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_397_, lean_object* v_p2_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Lake_Package_instBEq___lam__0(v_p1_397_, v_p2_398_);
lean_dec_ref(v_p2_398_);
lean_dec_ref(v_p1_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_403_){
_start:
{
lean_object* v_baseName_404_; uint8_t v___x_405_; lean_object* v___x_406_; 
v_baseName_404_ = lean_ctor_get(v_self_403_, 1);
lean_inc(v_baseName_404_);
lean_dec_ref(v_self_403_);
v___x_405_ = 0;
v___x_406_ = l_Lean_Name_toString(v_baseName_404_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_407_){
_start:
{
lean_object* v_keyName_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_keyName_408_ = lean_ctor_get(v_x_407_, 2);
lean_inc(v_keyName_408_);
lean_dec_ref(v_x_407_);
v___x_409_ = 1;
v___x_410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_408_, v___x_409_);
v___x_411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_414_){
_start:
{
lean_object* v_baseName_415_; uint8_t v___x_416_; lean_object* v___x_417_; 
v_baseName_415_ = lean_ctor_get(v_x_414_, 1);
lean_inc(v_baseName_415_);
lean_dec_ref(v_x_414_);
v___x_416_ = 0;
v___x_417_ = l_Lean_Name_toString(v_baseName_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_420_){
_start:
{
lean_object* v_baseName_421_; 
v_baseName_421_ = lean_ctor_get(v_self_420_, 1);
lean_inc(v_baseName_421_);
return v_baseName_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lake_Package_name(v_self_422_);
lean_dec_ref(v_self_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_424_){
_start:
{
lean_object* v_origName_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v_origName_425_ = lean_ctor_get(v_self_424_, 3);
lean_inc(v_origName_425_);
lean_dec_ref(v_self_424_);
v___x_426_ = 0;
v___x_427_ = l_Lean_Name_toString(v_origName_425_, v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_unsigned_to_nat(16u);
v___x_430_ = lean_mk_array(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_434_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_435_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(lean_object* v_self_437_){
_start:
{
lean_inc_ref(v_self_437_);
return v_self_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed(lean_object* v_self_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(v_self_438_);
lean_dec_ref(v_self_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg(){
_start:
{
lean_object* v___f_442_; 
v___f_442_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___boxed(lean_object* v___dummy_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_NPackage_instCoeOutPackage___redArg();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_445_){
_start:
{
lean_object* v___f_446_; 
v___f_446_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lake_NPackage_instCoeOutPackage(v_n_447_);
lean_dec(v_n_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_449_){
_start:
{
lean_inc_ref(v_pkg_449_);
return v_pkg_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_450_);
lean_dec_ref(v_pkg_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___y_454_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed(lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(v_x_458_, v___y_459_, v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v_x_458_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg(){
_start:
{
lean_object* v___f_465_; 
v___f_465_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___boxed(lean_object* v___dummy_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lake_instInhabitedPostUpdateHook_default___redArg();
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_468_){
_start:
{
lean_object* v___f_469_; 
v___f_469_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_470_);
lean_dec(v_pkgName_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg(){
_start:
{
lean_object* v___f_473_; 
v___f_473_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg___boxed(lean_object* v___dummy_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lake_instInhabitedPostUpdateHook___redArg();
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_476_){
_start:
{
lean_object* v___f_477_; 
v___f_477_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lake_instInhabitedPostUpdateHook(v_a_478_);
lean_dec(v_a_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_480_){
_start:
{
lean_inc_ref(v_a_480_);
return v_a_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_481_);
lean_dec_ref(v_a_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_483_, lean_object* v_a_484_){
_start:
{
lean_inc_ref(v_a_484_);
return v_a_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_485_, v_a_486_);
lean_dec_ref(v_a_486_);
lean_dec(v_name_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_489_, 0, v_name_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_490_){
_start:
{
lean_inc(v_a_490_);
return v_a_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_491_);
lean_dec(v_a_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_493_, lean_object* v_a_494_){
_start:
{
lean_inc(v_a_494_);
return v_a_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec(v_name_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_499_, 0, v_name_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_500_){
_start:
{
lean_inc_ref(v_inst_500_);
return v_inst_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_501_);
lean_dec_ref(v_inst_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_503_, lean_object* v_inst_504_){
_start:
{
lean_inc_ref(v_inst_504_);
return v_inst_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_505_, v_inst_506_);
lean_dec_ref(v_inst_506_);
lean_dec(v_name_505_);
return v_res_507_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_515_){
_start:
{
lean_object* v_wsIdx_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_wsIdx_516_ = lean_ctor_get(v_self_515_, 0);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_nat_dec_eq(v_wsIdx_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Lake_Package_isRoot(v_self_519_);
lean_dec_ref(v_self_519_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_522_){
_start:
{
lean_object* v_config_523_; uint8_t v_bootstrap_524_; 
v_config_523_ = lean_ctor_get(v_self_522_, 6);
v_bootstrap_524_ = lean_ctor_get_uint8(v_config_523_, sizeof(void*)*29);
return v_bootstrap_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_525_){
_start:
{
uint8_t v_res_526_; lean_object* v_r_527_; 
v_res_526_ = l_Lake_Package_bootstrap(v_self_525_);
lean_dec_ref(v_self_525_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_528_){
_start:
{
lean_object* v_config_529_; uint8_t v_bootstrap_530_; 
v_config_529_ = lean_ctor_get(v_self_528_, 6);
v_bootstrap_530_ = lean_ctor_get_uint8(v_config_529_, sizeof(void*)*29);
if (v_bootstrap_530_ == 0)
{
lean_object* v_origName_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_origName_531_ = lean_ctor_get(v_self_528_, 3);
lean_inc(v_origName_531_);
lean_dec_ref(v_self_528_);
v___x_532_ = l_Lean_Name_toString(v_origName_531_, v_bootstrap_530_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v_self_528_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_535_){
_start:
{
lean_object* v_config_536_; lean_object* v_version_537_; 
v_config_536_ = lean_ctor_get(v_self_535_, 6);
v_version_537_ = lean_ctor_get(v_config_536_, 17);
lean_inc_ref(v_version_537_);
return v_version_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_Package_version(v_self_538_);
lean_dec_ref(v_self_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_540_){
_start:
{
lean_object* v_config_541_; lean_object* v_versionTags_542_; 
v_config_541_ = lean_ctor_get(v_self_540_, 6);
v_versionTags_542_ = lean_ctor_get(v_config_541_, 18);
lean_inc_ref(v_versionTags_542_);
return v_versionTags_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lake_Package_versionTags(v_self_543_);
lean_dec_ref(v_self_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_545_){
_start:
{
lean_object* v_config_546_; lean_object* v_description_547_; 
v_config_546_ = lean_ctor_get(v_self_545_, 6);
v_description_547_ = lean_ctor_get(v_config_546_, 19);
lean_inc_ref(v_description_547_);
return v_description_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lake_Package_description(v_self_548_);
lean_dec_ref(v_self_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_550_){
_start:
{
lean_object* v_config_551_; lean_object* v_keywords_552_; 
v_config_551_ = lean_ctor_get(v_self_550_, 6);
v_keywords_552_ = lean_ctor_get(v_config_551_, 20);
lean_inc_ref(v_keywords_552_);
return v_keywords_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lake_Package_keywords(v_self_553_);
lean_dec_ref(v_self_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_555_){
_start:
{
lean_object* v_config_556_; lean_object* v_homepage_557_; 
v_config_556_ = lean_ctor_get(v_self_555_, 6);
v_homepage_557_ = lean_ctor_get(v_config_556_, 21);
lean_inc_ref(v_homepage_557_);
return v_homepage_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lake_Package_homepage(v_self_558_);
lean_dec_ref(v_self_558_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_560_){
_start:
{
lean_object* v_config_561_; uint8_t v_reservoir_562_; 
v_config_561_ = lean_ctor_get(v_self_560_, 6);
v_reservoir_562_ = lean_ctor_get_uint8(v_config_561_, sizeof(void*)*29 + 3);
return v_reservoir_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Lake_Package_reservoir(v_self_563_);
lean_dec_ref(v_self_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_566_){
_start:
{
lean_object* v_config_567_; lean_object* v_license_568_; 
v_config_567_ = lean_ctor_get(v_self_566_, 6);
v_license_568_ = lean_ctor_get(v_config_567_, 22);
lean_inc_ref(v_license_568_);
return v_license_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lake_Package_license(v_self_569_);
lean_dec_ref(v_self_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_591_){
_start:
{
lean_object* v_config_592_; lean_object* v_licenseFiles_593_; lean_object* v___f_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
v_config_592_ = lean_ctor_get(v_self_591_, 6);
lean_inc_ref(v_config_592_);
lean_dec_ref(v_self_591_);
v_licenseFiles_593_ = lean_ctor_get(v_config_592_, 23);
lean_inc_ref(v_licenseFiles_593_);
lean_dec_ref(v_config_592_);
v___f_594_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_595_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_596_ = lean_array_size(v_licenseFiles_593_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_595_, v___f_594_, v_sz_596_, v___x_597_, v_licenseFiles_593_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_599_, lean_object* v_x_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = l_System_FilePath_normalize(v_x_600_);
v___x_602_ = l_Lake_joinRelative(v_dir_599_, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_603_){
_start:
{
lean_object* v_config_604_; lean_object* v_dir_605_; lean_object* v_licenseFiles_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; size_t v_sz_610_; size_t v___x_611_; lean_object* v___x_612_; size_t v_sz_613_; lean_object* v___x_614_; 
v_config_604_ = lean_ctor_get(v_self_603_, 6);
lean_inc_ref(v_config_604_);
v_dir_605_ = lean_ctor_get(v_self_603_, 4);
lean_inc_ref(v_dir_605_);
lean_dec_ref(v_self_603_);
v_licenseFiles_606_ = lean_ctor_get(v_config_604_, 23);
lean_inc_ref(v_licenseFiles_606_);
lean_dec_ref(v_config_604_);
v___f_607_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_608_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_608_, 0, v_dir_605_);
v___x_609_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_610_ = lean_array_size(v_licenseFiles_606_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_609_, v___f_607_, v_sz_610_, v___x_611_, v_licenseFiles_606_);
v_sz_613_ = lean_array_size(v___x_612_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_609_, v___f_608_, v_sz_613_, v___x_611_, v___x_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_615_){
_start:
{
lean_object* v_config_616_; lean_object* v_readmeFile_617_; lean_object* v___x_618_; 
v_config_616_ = lean_ctor_get(v_self_615_, 6);
lean_inc_ref(v_config_616_);
lean_dec_ref(v_self_615_);
v_readmeFile_617_ = lean_ctor_get(v_config_616_, 24);
lean_inc_ref(v_readmeFile_617_);
lean_dec_ref(v_config_616_);
v___x_618_ = l_System_FilePath_normalize(v_readmeFile_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_619_){
_start:
{
lean_object* v_config_620_; lean_object* v_dir_621_; lean_object* v_readmeFile_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_config_620_ = lean_ctor_get(v_self_619_, 6);
lean_inc_ref(v_config_620_);
v_dir_621_ = lean_ctor_get(v_self_619_, 4);
lean_inc_ref(v_dir_621_);
lean_dec_ref(v_self_619_);
v_readmeFile_622_ = lean_ctor_get(v_config_620_, 24);
lean_inc_ref(v_readmeFile_622_);
lean_dec_ref(v_config_620_);
v___x_623_ = l_System_FilePath_normalize(v_readmeFile_622_);
v___x_624_ = l_Lake_joinRelative(v_dir_621_, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg(){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lake_defaultLakeDir;
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg___boxed(lean_object* v___dummy_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lake_Package_relLakeDir___redArg();
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lake_defaultLakeDir;
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lake_Package_relLakeDir(v_x_631_);
lean_dec_ref(v_x_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_633_){
_start:
{
lean_object* v_dir_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_dir_634_ = lean_ctor_get(v_self_633_, 4);
lean_inc_ref(v_dir_634_);
lean_dec_ref(v_self_633_);
v___x_635_ = l_Lake_defaultLakeDir;
v___x_636_ = l_Lake_joinRelative(v_dir_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_637_){
_start:
{
lean_object* v_config_638_; lean_object* v_toWorkspaceConfig_639_; lean_object* v___x_640_; 
v_config_638_ = lean_ctor_get(v_self_637_, 6);
lean_inc_ref(v_config_638_);
lean_dec_ref(v_self_637_);
v_toWorkspaceConfig_639_ = lean_ctor_get(v_config_638_, 0);
lean_inc_ref(v_toWorkspaceConfig_639_);
lean_dec_ref(v_config_638_);
v___x_640_ = l_System_FilePath_normalize(v_toWorkspaceConfig_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_641_){
_start:
{
lean_object* v_config_642_; lean_object* v_dir_643_; lean_object* v_toWorkspaceConfig_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_config_642_ = lean_ctor_get(v_self_641_, 6);
lean_inc_ref(v_config_642_);
v_dir_643_ = lean_ctor_get(v_self_641_, 4);
lean_inc_ref(v_dir_643_);
lean_dec_ref(v_self_641_);
v_toWorkspaceConfig_644_ = lean_ctor_get(v_config_642_, 0);
lean_inc_ref(v_toWorkspaceConfig_644_);
lean_dec_ref(v_config_642_);
v___x_645_ = l_System_FilePath_normalize(v_toWorkspaceConfig_644_);
v___x_646_ = l_Lake_joinRelative(v_dir_643_, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_647_){
_start:
{
lean_object* v_dir_648_; lean_object* v_relManifestFile_649_; lean_object* v___x_650_; 
v_dir_648_ = lean_ctor_get(v_self_647_, 4);
lean_inc_ref(v_dir_648_);
v_relManifestFile_649_ = lean_ctor_get(v_self_647_, 9);
lean_inc_ref(v_relManifestFile_649_);
lean_dec_ref(v_self_647_);
v___x_650_ = l_Lake_joinRelative(v_dir_648_, v_relManifestFile_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_651_){
_start:
{
lean_object* v_config_652_; lean_object* v_dir_653_; lean_object* v_buildDir_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_config_652_ = lean_ctor_get(v_self_651_, 6);
lean_inc_ref(v_config_652_);
v_dir_653_ = lean_ctor_get(v_self_651_, 4);
lean_inc_ref(v_dir_653_);
lean_dec_ref(v_self_651_);
v_buildDir_654_ = lean_ctor_get(v_config_652_, 5);
lean_inc_ref(v_buildDir_654_);
lean_dec_ref(v_config_652_);
v___x_655_ = l_System_FilePath_normalize(v_buildDir_654_);
v___x_656_ = l_Lake_joinRelative(v_dir_653_, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_657_){
_start:
{
lean_object* v_config_658_; lean_object* v_testDriverArgs_659_; 
v_config_658_ = lean_ctor_get(v_self_657_, 6);
v_testDriverArgs_659_ = lean_ctor_get(v_config_658_, 14);
lean_inc_ref(v_testDriverArgs_659_);
return v_testDriverArgs_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lake_Package_testDriverArgs(v_self_660_);
lean_dec_ref(v_self_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_662_){
_start:
{
lean_object* v_config_663_; lean_object* v_lintDriverArgs_664_; 
v_config_663_ = lean_ctor_get(v_self_662_, 6);
v_lintDriverArgs_664_ = lean_ctor_get(v_config_663_, 16);
lean_inc_ref(v_lintDriverArgs_664_);
return v_lintDriverArgs_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_Package_lintDriverArgs(v_self_665_);
lean_dec_ref(v_self_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_667_){
_start:
{
lean_object* v_config_668_; lean_object* v_extraDepTargets_669_; 
v_config_668_ = lean_ctor_get(v_self_667_, 6);
v_extraDepTargets_669_ = lean_ctor_get(v_config_668_, 2);
lean_inc_ref(v_extraDepTargets_669_);
return v_extraDepTargets_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lake_Package_extraDepTargets(v_self_670_);
lean_dec_ref(v_self_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_672_){
_start:
{
lean_object* v_config_673_; lean_object* v_toLeanConfig_674_; lean_object* v_platformIndependent_675_; 
v_config_673_ = lean_ctor_get(v_self_672_, 6);
v_toLeanConfig_674_ = lean_ctor_get(v_config_673_, 1);
v_platformIndependent_675_ = lean_ctor_get(v_toLeanConfig_674_, 10);
lean_inc(v_platformIndependent_675_);
return v_platformIndependent_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lake_Package_platformIndependent(v_self_676_);
lean_dec_ref(v_self_676_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_684_){
_start:
{
lean_object* v_config_685_; lean_object* v_toLeanConfig_686_; lean_object* v_platformIndependent_687_; lean_object* v___f_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_config_685_ = lean_ctor_get(v_self_684_, 6);
lean_inc_ref(v_config_685_);
lean_dec_ref(v_self_684_);
v_toLeanConfig_686_ = lean_ctor_get(v_config_685_, 1);
lean_inc_ref(v_toLeanConfig_686_);
lean_dec_ref(v_config_685_);
v_platformIndependent_687_ = lean_ctor_get(v_toLeanConfig_686_, 10);
lean_inc(v_platformIndependent_687_);
lean_dec_ref(v_toLeanConfig_686_);
v___f_688_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_689_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_690_ = l_instBEqOption_beq___redArg(v___f_688_, v_platformIndependent_687_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lake_Package_isPlatformIndependent(v_self_691_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_694_){
_start:
{
lean_object* v_config_695_; uint8_t v_fixedToolchain_696_; 
v_config_695_ = lean_ctor_get(v_self_694_, 6);
v_fixedToolchain_696_ = lean_ctor_get_uint8(v_config_695_, sizeof(void*)*29 + 6);
return v_fixedToolchain_696_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lake_Package_fixedToolchain(v_self_697_);
lean_dec_ref(v_self_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_700_){
_start:
{
lean_object* v_config_701_; lean_object* v_releaseRepo_702_; 
v_config_701_ = lean_ctor_get(v_self_700_, 6);
v_releaseRepo_702_ = lean_ctor_get(v_config_701_, 10);
lean_inc(v_releaseRepo_702_);
return v_releaseRepo_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lake_Package_releaseRepo_x3f(v_self_703_);
lean_dec_ref(v_self_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_705_){
_start:
{
lean_object* v_remoteUrl_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_remoteUrl_706_ = lean_ctor_get(v_self_705_, 11);
v___x_707_ = lean_string_utf8_byte_size(v_remoteUrl_706_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_eq(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_inc_ref(v_remoteUrl_706_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_remoteUrl_706_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(0);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lake_Package_remoteUrl_x3f(v_self_712_);
lean_dec_ref(v_self_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_714_){
_start:
{
lean_object* v_dir_715_; lean_object* v_buildArchive_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_dir_715_ = lean_ctor_get(v_self_714_, 4);
lean_inc_ref(v_dir_715_);
v_buildArchive_716_ = lean_ctor_get(v_self_714_, 22);
lean_inc_ref(v_buildArchive_716_);
lean_dec_ref(v_self_714_);
v___x_717_ = l_Lake_defaultLakeDir;
v___x_718_ = l_Lake_joinRelative(v_dir_715_, v___x_717_);
v___x_719_ = l_Lake_joinRelative(v___x_718_, v_buildArchive_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_721_){
_start:
{
lean_object* v_dir_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_dir_722_ = lean_ctor_get(v_self_721_, 4);
lean_inc_ref(v_dir_722_);
lean_dec_ref(v_self_721_);
v___x_723_ = l_Lake_defaultLakeDir;
v___x_724_ = l_Lake_joinRelative(v_dir_722_, v___x_723_);
v___x_725_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_726_ = l_Lake_joinRelative(v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_727_){
_start:
{
lean_object* v_config_728_; uint8_t v_preferReleaseBuild_729_; 
v_config_728_ = lean_ctor_get(v_self_727_, 6);
v_preferReleaseBuild_729_ = lean_ctor_get_uint8(v_config_728_, sizeof(void*)*29 + 2);
return v_preferReleaseBuild_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Lake_Package_preferReleaseBuild(v_self_730_);
lean_dec_ref(v_self_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_downloadCacheService_x3f(lean_object* v_self_733_){
_start:
{
lean_object* v_config_734_; lean_object* v_downloadCacheService_x3f_735_; 
v_config_734_ = lean_ctor_get(v_self_733_, 6);
lean_inc_ref(v_config_734_);
lean_dec_ref(v_self_733_);
v_downloadCacheService_x3f_735_ = lean_ctor_get(v_config_734_, 12);
lean_inc(v_downloadCacheService_x3f_735_);
lean_dec_ref(v_config_734_);
if (lean_obj_tag(v_downloadCacheService_x3f_735_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
else
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_val_737_ = lean_ctor_get(v_downloadCacheService_x3f_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_downloadCacheService_x3f_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v_downloadCacheService_x3f_735_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v_downloadCacheService_x3f_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_745_){
_start:
{
lean_object* v_config_746_; uint8_t v_precompileModules_747_; 
v_config_746_ = lean_ctor_get(v_self_745_, 6);
v_precompileModules_747_ = lean_ctor_get_uint8(v_config_746_, sizeof(void*)*29 + 1);
return v_precompileModules_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lake_Package_precompileModules(v_self_748_);
lean_dec_ref(v_self_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileImports(lean_object* v_self_751_){
_start:
{
lean_object* v_config_752_; lean_object* v_toLeanConfig_753_; uint8_t v_precompileImports_754_; 
v_config_752_ = lean_ctor_get(v_self_751_, 6);
v_toLeanConfig_753_ = lean_ctor_get(v_config_752_, 1);
v_precompileImports_754_ = lean_ctor_get_uint8(v_toLeanConfig_753_, sizeof(void*)*13 + 2);
return v_precompileImports_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileImports___boxed(lean_object* v_self_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lake_Package_precompileImports(v_self_755_);
lean_dec_ref(v_self_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_758_){
_start:
{
lean_object* v_config_759_; lean_object* v_moreGlobalServerArgs_760_; 
v_config_759_ = lean_ctor_get(v_self_758_, 6);
v_moreGlobalServerArgs_760_ = lean_ctor_get(v_config_759_, 3);
lean_inc_ref(v_moreGlobalServerArgs_760_);
return v_moreGlobalServerArgs_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_Package_moreGlobalServerArgs(v_self_761_);
lean_dec_ref(v_self_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_763_){
_start:
{
lean_object* v_config_764_; lean_object* v_toLeanConfig_765_; lean_object* v_leanOptions_766_; lean_object* v_moreServerOptions_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_config_764_ = lean_ctor_get(v_self_763_, 6);
v_toLeanConfig_765_ = lean_ctor_get(v_config_764_, 1);
v_leanOptions_766_ = lean_ctor_get(v_toLeanConfig_765_, 0);
v_moreServerOptions_767_ = lean_ctor_get(v_toLeanConfig_765_, 4);
v___x_768_ = l_Lean_LeanOptions_ofArray(v_leanOptions_766_);
v___x_769_ = l_Lean_LeanOptions_appendArray(v___x_768_, v_moreServerOptions_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lake_Package_moreServerOptions(v_self_770_);
lean_dec_ref(v_self_770_);
return v_res_771_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_772_){
_start:
{
lean_object* v_config_773_; lean_object* v_toLeanConfig_774_; uint8_t v_buildType_775_; 
v_config_773_ = lean_ctor_get(v_self_772_, 6);
v_toLeanConfig_774_ = lean_ctor_get(v_config_773_, 1);
v_buildType_775_ = lean_ctor_get_uint8(v_toLeanConfig_774_, sizeof(void*)*13);
return v_buildType_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Lake_Package_buildType(v_self_776_);
lean_dec_ref(v_self_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_779_){
_start:
{
lean_object* v_config_780_; lean_object* v_toLeanConfig_781_; uint8_t v_backend_782_; 
v_config_780_ = lean_ctor_get(v_self_779_, 6);
v_toLeanConfig_781_ = lean_ctor_get(v_config_780_, 1);
v_backend_782_ = lean_ctor_get_uint8(v_toLeanConfig_781_, sizeof(void*)*13 + 1);
return v_backend_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lake_Package_backend(v_self_783_);
lean_dec_ref(v_self_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_786_){
_start:
{
lean_object* v_config_787_; uint8_t v_allowImportAll_788_; 
v_config_787_ = lean_ctor_get(v_self_786_, 6);
v_allowImportAll_788_ = lean_ctor_get_uint8(v_config_787_, sizeof(void*)*29 + 5);
return v_allowImportAll_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Lake_Package_allowImportAll(v_self_789_);
lean_dec_ref(v_self_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_792_){
_start:
{
lean_object* v_config_793_; lean_object* v_toLeanConfig_794_; uint8_t v_requiresModuleSystem_795_; 
v_config_793_ = lean_ctor_get(v_self_792_, 6);
v_toLeanConfig_794_ = lean_ctor_get(v_config_793_, 1);
v_requiresModuleSystem_795_ = lean_ctor_get_uint8(v_toLeanConfig_794_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Lake_Package_requiresModuleSystem(v_self_796_);
lean_dec_ref(v_self_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_799_){
_start:
{
lean_object* v_config_800_; lean_object* v_toLeanConfig_801_; uint8_t v_allowNonModules_802_; 
v_config_800_ = lean_ctor_get(v_self_799_, 6);
v_toLeanConfig_801_ = lean_ctor_get(v_config_800_, 1);
v_allowNonModules_802_ = lean_ctor_get_uint8(v_toLeanConfig_801_, sizeof(void*)*13 + 4);
return v_allowNonModules_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lake_Package_allowNonModules(v_self_803_);
lean_dec_ref(v_self_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_806_){
_start:
{
lean_object* v_config_807_; lean_object* v_toLeanConfig_808_; lean_object* v_dynlibs_809_; 
v_config_807_ = lean_ctor_get(v_self_806_, 6);
v_toLeanConfig_808_ = lean_ctor_get(v_config_807_, 1);
v_dynlibs_809_ = lean_ctor_get(v_toLeanConfig_808_, 11);
lean_inc_ref(v_dynlibs_809_);
return v_dynlibs_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lake_Package_dynlibs(v_self_810_);
lean_dec_ref(v_self_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_812_){
_start:
{
lean_object* v_config_813_; lean_object* v_toLeanConfig_814_; lean_object* v_plugins_815_; 
v_config_813_ = lean_ctor_get(v_self_812_, 6);
v_toLeanConfig_814_ = lean_ctor_get(v_config_813_, 1);
v_plugins_815_ = lean_ctor_get(v_toLeanConfig_814_, 12);
lean_inc_ref(v_plugins_815_);
return v_plugins_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_Package_plugins(v_self_816_);
lean_dec_ref(v_self_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_818_){
_start:
{
lean_object* v_config_819_; lean_object* v_toLeanConfig_820_; lean_object* v_leanOptions_821_; lean_object* v___x_822_; 
v_config_819_ = lean_ctor_get(v_self_818_, 6);
v_toLeanConfig_820_ = lean_ctor_get(v_config_819_, 1);
v_leanOptions_821_ = lean_ctor_get(v_toLeanConfig_820_, 0);
v___x_822_ = l_Lean_LeanOptions_ofArray(v_leanOptions_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lake_Package_leanOptions(v_self_823_);
lean_dec_ref(v_self_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_825_){
_start:
{
lean_object* v_config_826_; lean_object* v_toLeanConfig_827_; lean_object* v_moreLeanArgs_828_; 
v_config_826_ = lean_ctor_get(v_self_825_, 6);
v_toLeanConfig_827_ = lean_ctor_get(v_config_826_, 1);
v_moreLeanArgs_828_ = lean_ctor_get(v_toLeanConfig_827_, 1);
lean_inc_ref(v_moreLeanArgs_828_);
return v_moreLeanArgs_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lake_Package_moreLeanArgs(v_self_829_);
lean_dec_ref(v_self_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_831_){
_start:
{
lean_object* v_config_832_; lean_object* v_toLeanConfig_833_; lean_object* v_weakLeanArgs_834_; 
v_config_832_ = lean_ctor_get(v_self_831_, 6);
v_toLeanConfig_833_ = lean_ctor_get(v_config_832_, 1);
v_weakLeanArgs_834_ = lean_ctor_get(v_toLeanConfig_833_, 2);
lean_inc_ref(v_weakLeanArgs_834_);
return v_weakLeanArgs_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lake_Package_weakLeanArgs(v_self_835_);
lean_dec_ref(v_self_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_837_){
_start:
{
lean_object* v_config_838_; lean_object* v_toLeanConfig_839_; lean_object* v_moreLeancArgs_840_; 
v_config_838_ = lean_ctor_get(v_self_837_, 6);
v_toLeanConfig_839_ = lean_ctor_get(v_config_838_, 1);
v_moreLeancArgs_840_ = lean_ctor_get(v_toLeanConfig_839_, 3);
lean_inc_ref(v_moreLeancArgs_840_);
return v_moreLeancArgs_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_Package_moreLeancArgs(v_self_841_);
lean_dec_ref(v_self_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_843_){
_start:
{
lean_object* v_config_844_; lean_object* v_toLeanConfig_845_; lean_object* v_weakLeancArgs_846_; 
v_config_844_ = lean_ctor_get(v_self_843_, 6);
v_toLeanConfig_845_ = lean_ctor_get(v_config_844_, 1);
v_weakLeancArgs_846_ = lean_ctor_get(v_toLeanConfig_845_, 5);
lean_inc_ref(v_weakLeancArgs_846_);
return v_weakLeancArgs_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lake_Package_weakLeancArgs(v_self_847_);
lean_dec_ref(v_self_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_849_){
_start:
{
lean_object* v_config_850_; lean_object* v_toLeanConfig_851_; lean_object* v_moreLinkObjs_852_; 
v_config_850_ = lean_ctor_get(v_self_849_, 6);
v_toLeanConfig_851_ = lean_ctor_get(v_config_850_, 1);
v_moreLinkObjs_852_ = lean_ctor_get(v_toLeanConfig_851_, 6);
lean_inc_ref(v_moreLinkObjs_852_);
return v_moreLinkObjs_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lake_Package_moreLinkObjs(v_self_853_);
lean_dec_ref(v_self_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_855_){
_start:
{
lean_object* v_config_856_; lean_object* v_toLeanConfig_857_; lean_object* v_moreLinkLibs_858_; 
v_config_856_ = lean_ctor_get(v_self_855_, 6);
v_toLeanConfig_857_ = lean_ctor_get(v_config_856_, 1);
v_moreLinkLibs_858_ = lean_ctor_get(v_toLeanConfig_857_, 7);
lean_inc_ref(v_moreLinkLibs_858_);
return v_moreLinkLibs_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lake_Package_moreLinkLibs(v_self_859_);
lean_dec_ref(v_self_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_861_){
_start:
{
lean_object* v_config_862_; lean_object* v_toLeanConfig_863_; lean_object* v_moreLinkArgs_864_; 
v_config_862_ = lean_ctor_get(v_self_861_, 6);
v_toLeanConfig_863_ = lean_ctor_get(v_config_862_, 1);
v_moreLinkArgs_864_ = lean_ctor_get(v_toLeanConfig_863_, 8);
lean_inc_ref(v_moreLinkArgs_864_);
return v_moreLinkArgs_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_Package_moreLinkArgs(v_self_865_);
lean_dec_ref(v_self_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_867_){
_start:
{
lean_object* v_config_868_; lean_object* v_toLeanConfig_869_; lean_object* v_weakLinkArgs_870_; 
v_config_868_ = lean_ctor_get(v_self_867_, 6);
v_toLeanConfig_869_ = lean_ctor_get(v_config_868_, 1);
v_weakLinkArgs_870_ = lean_ctor_get(v_toLeanConfig_869_, 9);
lean_inc_ref(v_weakLinkArgs_870_);
return v_weakLinkArgs_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lake_Package_weakLinkArgs(v_self_871_);
lean_dec_ref(v_self_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_873_){
_start:
{
lean_object* v_config_874_; lean_object* v_dir_875_; lean_object* v_srcDir_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_config_874_ = lean_ctor_get(v_self_873_, 6);
lean_inc_ref(v_config_874_);
v_dir_875_ = lean_ctor_get(v_self_873_, 4);
lean_inc_ref(v_dir_875_);
lean_dec_ref(v_self_873_);
v_srcDir_876_ = lean_ctor_get(v_config_874_, 4);
lean_inc_ref(v_srcDir_876_);
lean_dec_ref(v_config_874_);
v___x_877_ = l_System_FilePath_normalize(v_srcDir_876_);
v___x_878_ = l_Lake_joinRelative(v_dir_875_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_879_){
_start:
{
lean_object* v_config_880_; lean_object* v_dir_881_; lean_object* v_srcDir_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_config_880_ = lean_ctor_get(v_self_879_, 6);
lean_inc_ref(v_config_880_);
v_dir_881_ = lean_ctor_get(v_self_879_, 4);
lean_inc_ref(v_dir_881_);
lean_dec_ref(v_self_879_);
v_srcDir_882_ = lean_ctor_get(v_config_880_, 4);
lean_inc_ref(v_srcDir_882_);
lean_dec_ref(v_config_880_);
v___x_883_ = l_System_FilePath_normalize(v_srcDir_882_);
v___x_884_ = l_Lake_joinRelative(v_dir_881_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_885_){
_start:
{
lean_object* v_config_886_; lean_object* v_dir_887_; lean_object* v_buildDir_888_; lean_object* v_leanLibDir_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_config_886_ = lean_ctor_get(v_self_885_, 6);
lean_inc_ref(v_config_886_);
v_dir_887_ = lean_ctor_get(v_self_885_, 4);
lean_inc_ref(v_dir_887_);
lean_dec_ref(v_self_885_);
v_buildDir_888_ = lean_ctor_get(v_config_886_, 5);
lean_inc_ref(v_buildDir_888_);
v_leanLibDir_889_ = lean_ctor_get(v_config_886_, 6);
lean_inc_ref(v_leanLibDir_889_);
lean_dec_ref(v_config_886_);
v___x_890_ = l_System_FilePath_normalize(v_buildDir_888_);
v___x_891_ = l_Lake_joinRelative(v_dir_887_, v___x_890_);
v___x_892_ = l_System_FilePath_normalize(v_leanLibDir_889_);
v___x_893_ = l_Lake_joinRelative(v___x_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object* v_self_895_){
_start:
{
lean_object* v_config_896_; lean_object* v_dir_897_; lean_object* v_buildDir_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_config_896_ = lean_ctor_get(v_self_895_, 6);
lean_inc_ref(v_config_896_);
v_dir_897_ = lean_ctor_get(v_self_895_, 4);
lean_inc_ref(v_dir_897_);
lean_dec_ref(v_self_895_);
v_buildDir_898_ = lean_ctor_get(v_config_896_, 5);
lean_inc_ref(v_buildDir_898_);
lean_dec_ref(v_config_896_);
v___x_899_ = l_System_FilePath_normalize(v_buildDir_898_);
v___x_900_ = l_Lake_joinRelative(v_dir_897_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lake_Package_bootstrapIncludeDir___closed__0));
v___x_902_ = l_Lake_joinRelative(v___x_900_, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_903_){
_start:
{
lean_object* v_config_904_; lean_object* v_dir_905_; lean_object* v_buildDir_906_; lean_object* v_nativeLibDir_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_config_904_ = lean_ctor_get(v_self_903_, 6);
lean_inc_ref(v_config_904_);
v_dir_905_ = lean_ctor_get(v_self_903_, 4);
lean_inc_ref(v_dir_905_);
lean_dec_ref(v_self_903_);
v_buildDir_906_ = lean_ctor_get(v_config_904_, 5);
lean_inc_ref(v_buildDir_906_);
v_nativeLibDir_907_ = lean_ctor_get(v_config_904_, 7);
lean_inc_ref(v_nativeLibDir_907_);
lean_dec_ref(v_config_904_);
v___x_908_ = l_System_FilePath_normalize(v_buildDir_906_);
v___x_909_ = l_Lake_joinRelative(v_dir_905_, v___x_908_);
v___x_910_ = l_System_FilePath_normalize(v_nativeLibDir_907_);
v___x_911_ = l_Lake_joinRelative(v___x_909_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_912_){
_start:
{
lean_object* v_config_913_; lean_object* v_dir_914_; lean_object* v_buildDir_915_; lean_object* v_nativeLibDir_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_config_913_ = lean_ctor_get(v_self_912_, 6);
lean_inc_ref(v_config_913_);
v_dir_914_ = lean_ctor_get(v_self_912_, 4);
lean_inc_ref(v_dir_914_);
lean_dec_ref(v_self_912_);
v_buildDir_915_ = lean_ctor_get(v_config_913_, 5);
lean_inc_ref(v_buildDir_915_);
v_nativeLibDir_916_ = lean_ctor_get(v_config_913_, 7);
lean_inc_ref(v_nativeLibDir_916_);
lean_dec_ref(v_config_913_);
v___x_917_ = l_System_FilePath_normalize(v_buildDir_915_);
v___x_918_ = l_Lake_joinRelative(v_dir_914_, v___x_917_);
v___x_919_ = l_System_FilePath_normalize(v_nativeLibDir_916_);
v___x_920_ = l_Lake_joinRelative(v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_921_){
_start:
{
lean_object* v_config_922_; lean_object* v_dir_923_; lean_object* v_buildDir_924_; lean_object* v_binDir_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_config_922_ = lean_ctor_get(v_self_921_, 6);
lean_inc_ref(v_config_922_);
v_dir_923_ = lean_ctor_get(v_self_921_, 4);
lean_inc_ref(v_dir_923_);
lean_dec_ref(v_self_921_);
v_buildDir_924_ = lean_ctor_get(v_config_922_, 5);
lean_inc_ref(v_buildDir_924_);
v_binDir_925_ = lean_ctor_get(v_config_922_, 8);
lean_inc_ref(v_binDir_925_);
lean_dec_ref(v_config_922_);
v___x_926_ = l_System_FilePath_normalize(v_buildDir_924_);
v___x_927_ = l_Lake_joinRelative(v_dir_923_, v___x_926_);
v___x_928_ = l_System_FilePath_normalize(v_binDir_925_);
v___x_929_ = l_Lake_joinRelative(v___x_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_930_){
_start:
{
lean_object* v_config_931_; lean_object* v_dir_932_; lean_object* v_buildDir_933_; lean_object* v_irDir_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_config_931_ = lean_ctor_get(v_self_930_, 6);
lean_inc_ref(v_config_931_);
v_dir_932_ = lean_ctor_get(v_self_930_, 4);
lean_inc_ref(v_dir_932_);
lean_dec_ref(v_self_930_);
v_buildDir_933_ = lean_ctor_get(v_config_931_, 5);
lean_inc_ref(v_buildDir_933_);
v_irDir_934_ = lean_ctor_get(v_config_931_, 9);
lean_inc_ref(v_irDir_934_);
lean_dec_ref(v_config_931_);
v___x_935_ = l_System_FilePath_normalize(v_buildDir_933_);
v___x_936_ = l_Lake_joinRelative(v_dir_932_, v___x_935_);
v___x_937_ = l_System_FilePath_normalize(v_irDir_934_);
v___x_938_ = l_Lake_joinRelative(v___x_936_, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_939_){
_start:
{
lean_object* v_config_940_; uint8_t v_libPrefixOnWindows_941_; 
v_config_940_ = lean_ctor_get(v_self_939_, 6);
v_libPrefixOnWindows_941_ = lean_ctor_get_uint8(v_config_940_, sizeof(void*)*29 + 4);
return v_libPrefixOnWindows_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lake_Package_libPrefixOnWindows(v_self_942_);
lean_dec_ref(v_self_942_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_945_){
_start:
{
lean_object* v_config_946_; lean_object* v_enableArtifactCache_x3f_947_; 
v_config_946_ = lean_ctor_get(v_self_945_, 6);
v_enableArtifactCache_x3f_947_ = lean_ctor_get(v_config_946_, 25);
lean_inc(v_enableArtifactCache_x3f_947_);
return v_enableArtifactCache_x3f_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lake_Package_enableArtifactCache_x3f(v_self_948_);
lean_dec_ref(v_self_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_950_){
_start:
{
lean_object* v_config_951_; lean_object* v_restoreAllArtifacts_x3f_952_; 
v_config_951_ = lean_ctor_get(v_self_950_, 6);
v_restoreAllArtifacts_x3f_952_ = lean_ctor_get(v_config_951_, 26);
lean_inc(v_restoreAllArtifacts_x3f_952_);
return v_restoreAllArtifacts_x3f_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_953_);
lean_dec_ref(v_self_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_955_){
_start:
{
lean_object* v_baseName_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v_baseName_956_ = lean_ctor_get(v_self_955_, 1);
lean_inc(v_baseName_956_);
lean_dec_ref(v_self_955_);
v___x_957_ = 0;
v___x_958_ = l_Lean_Name_toString(v_baseName_956_, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_cacheToolchain(lean_object* v_pkg_959_, lean_object* v_toolchain_960_){
_start:
{
lean_object* v_config_961_; uint8_t v_fixedToolchain_962_; 
v_config_961_ = lean_ctor_get(v_pkg_959_, 6);
v_fixedToolchain_962_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*29 + 6);
if (v_fixedToolchain_962_ == 0)
{
uint8_t v_bootstrap_963_; 
v_bootstrap_963_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*29);
if (v_bootstrap_963_ == 0)
{
lean_inc_ref(v_toolchain_960_);
return v_toolchain_960_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = l_Lake_CacheToolchain_none;
return v___x_964_;
}
}
else
{
lean_object* v___x_965_; 
v___x_965_ = l_Lake_CacheToolchain_none;
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_cacheToolchain___boxed(lean_object* v_pkg_966_, lean_object* v_toolchain_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_Internal_cacheToolchain(v_pkg_966_, v_toolchain_967_);
lean_dec_ref(v_toolchain_967_);
lean_dec_ref(v_pkg_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_cachePlatform(lean_object* v_pkg_969_, lean_object* v_platform_970_){
_start:
{
lean_object* v_config_971_; lean_object* v_toLeanConfig_972_; lean_object* v_platformIndependent_973_; lean_object* v___f_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_config_971_ = lean_ctor_get(v_pkg_969_, 6);
lean_inc_ref(v_config_971_);
lean_dec_ref(v_pkg_969_);
v_toLeanConfig_972_ = lean_ctor_get(v_config_971_, 1);
lean_inc_ref(v_toLeanConfig_972_);
lean_dec_ref(v_config_971_);
v_platformIndependent_973_ = lean_ctor_get(v_toLeanConfig_972_, 10);
lean_inc(v_platformIndependent_973_);
lean_dec_ref(v_toLeanConfig_972_);
v___f_974_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_975_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_976_ = l_instBEqOption_beq___redArg(v___f_974_, v_platformIndependent_973_, v___x_975_);
if (v___x_976_ == 0)
{
lean_inc_ref(v_platform_970_);
return v_platform_970_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l_Lake_CachePlatform_none;
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_cachePlatform___boxed(lean_object* v_pkg_978_, lean_object* v_platform_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lake_Internal_cachePlatform(v_pkg_978_, v_platform_979_);
lean_dec_ref(v_platform_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_982_){
_start:
{
lean_object* v_origName_983_; lean_object* v_scope_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_origName_983_ = lean_ctor_get(v_self_982_, 3);
lean_inc(v_origName_983_);
v_scope_984_ = lean_ctor_get(v_self_982_, 10);
lean_inc_ref(v_scope_984_);
lean_dec_ref(v_self_982_);
v___x_985_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_986_ = lean_string_append(v_scope_984_, v___x_985_);
v___x_987_ = 0;
v___x_988_ = l_Lean_Name_toString(v_origName_983_, v___x_987_);
v___x_989_ = lean_string_append(v___x_986_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_991_){
_start:
{
lean_object* v_scope_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_scope_992_ = lean_ctor_get(v_self_991_, 10);
v___x_993_ = lean_string_utf8_byte_size(v_scope_992_);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_nat_dec_eq(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_991_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; 
lean_dec_ref(v_self_991_);
v___x_998_ = lean_box(0);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_999_, lean_object* v_k_1000_){
_start:
{
if (lean_obj_tag(v_t_999_) == 0)
{
lean_object* v_k_1001_; lean_object* v_v_1002_; lean_object* v_l_1003_; lean_object* v_r_1004_; uint8_t v___x_1005_; 
v_k_1001_ = lean_ctor_get(v_t_999_, 1);
v_v_1002_ = lean_ctor_get(v_t_999_, 2);
v_l_1003_ = lean_ctor_get(v_t_999_, 3);
v_r_1004_ = lean_ctor_get(v_t_999_, 4);
v___x_1005_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1000_, v_k_1001_);
switch(v___x_1005_)
{
case 0:
{
v_t_999_ = v_l_1003_;
goto _start;
}
case 1:
{
lean_object* v___x_1007_; 
lean_inc(v_v_1002_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_v_1002_);
return v___x_1007_;
}
default: 
{
v_t_999_ = v_r_1004_;
goto _start;
}
}
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_1010_, lean_object* v_k_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1010_, v_k_1011_);
lean_dec(v_k_1011_);
lean_dec(v_t_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_1013_, lean_object* v_self_1014_){
_start:
{
lean_object* v_targetDeclMap_1015_; lean_object* v___x_1016_; 
v_targetDeclMap_1015_ = lean_ctor_get(v_self_1014_, 16);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_1015_, v_name_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_1017_, lean_object* v_self_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lake_Package_findTargetDecl_x3f(v_name_1017_, v_self_1018_);
lean_dec_ref(v_self_1018_);
lean_dec(v_name_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_1020_, lean_object* v_inst_1021_, lean_object* v_t_1022_, lean_object* v_k_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1022_, v_k_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_inst_1026_, lean_object* v_t_1027_, lean_object* v_k_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_1025_, v_inst_1026_, v_t_1027_, v_k_1028_);
lean_dec(v_k_1028_);
lean_dec(v_t_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_1033_, lean_object* v_as_1034_, size_t v_i_1035_, size_t v_stop_1036_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_eq(v_i_1035_, v_stop_1036_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v_kind_1043_; lean_object* v_config_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1042_ = lean_array_uget_borrowed(v_as_1034_, v_i_1035_);
v_kind_1043_ = lean_ctor_get(v___x_1042_, 2);
v_config_1044_ = lean_ctor_get(v___x_1042_, 3);
v___x_1045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1046_ = lean_name_eq(v_kind_1043_, v___x_1045_);
if (v___x_1046_ == 0)
{
goto v___jp_1037_;
}
else
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1033_, v_config_1044_);
if (v___x_1047_ == 0)
{
goto v___jp_1037_;
}
else
{
return v___x_1047_;
}
}
}
else
{
uint8_t v___x_1048_; 
v___x_1048_ = 0;
return v___x_1048_;
}
v___jp_1037_:
{
size_t v___x_1038_; size_t v___x_1039_; 
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1035_, v___x_1038_);
v_i_1035_ = v___x_1039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_1049_, lean_object* v_as_1050_, lean_object* v_i_1051_, lean_object* v_stop_1052_){
_start:
{
size_t v_i_boxed_1053_; size_t v_stop_boxed_1054_; uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_i_boxed_1053_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_stop_boxed_1054_ = lean_unbox_usize(v_stop_1052_);
lean_dec(v_stop_1052_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1049_, v_as_1050_, v_i_boxed_1053_, v_stop_boxed_1054_);
lean_dec_ref(v_as_1050_);
lean_dec(v_mod_1049_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_1057_, lean_object* v_self_1058_){
_start:
{
lean_object* v_targetDecls_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_targetDecls_1059_ = lean_ctor_get(v_self_1058_, 15);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_array_get_size(v_targetDecls_1059_);
v___x_1062_ = lean_nat_dec_lt(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
return v___x_1062_;
}
else
{
if (v___x_1062_ == 0)
{
return v___x_1062_;
}
else
{
size_t v___x_1063_; size_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1061_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1057_, v_targetDecls_1059_, v___x_1063_, v___x_1064_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1066_, lean_object* v_self_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l_Lake_Package_isLocalModule(v_mod_1066_, v_self_1067_);
lean_dec_ref(v_self_1067_);
lean_dec(v_mod_1066_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1070_, lean_object* v_as_1071_, size_t v_i_1072_, size_t v_stop_1073_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1072_, v_stop_1073_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v_kind_1080_; lean_object* v_config_1081_; uint8_t v___x_1082_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1071_, v_i_1072_);
v_kind_1080_ = lean_ctor_get(v___x_1079_, 2);
v_config_1081_ = lean_ctor_get(v___x_1079_, 3);
v___x_1082_ = 1;
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1089_ = lean_name_eq(v_kind_1080_, v___x_1088_);
if (v___x_1089_ == 0)
{
goto v___jp_1083_;
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1070_, v_config_1081_);
if (v___x_1090_ == 0)
{
goto v___jp_1083_;
}
else
{
return v___x_1082_;
}
}
v___jp_1083_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = l_Lake_LeanExe_keyword;
v___x_1085_ = lean_name_eq(v_kind_1080_, v___x_1084_);
if (v___x_1085_ == 0)
{
goto v___jp_1074_;
}
else
{
lean_object* v_root_1086_; uint8_t v___x_1087_; 
v_root_1086_ = lean_ctor_get(v_config_1081_, 2);
v___x_1087_ = lean_name_eq(v_root_1086_, v_mod_1070_);
if (v___x_1087_ == 0)
{
goto v___jp_1074_;
}
else
{
return v___x_1082_;
}
}
}
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = 0;
return v___x_1091_;
}
v___jp_1074_:
{
size_t v___x_1075_; size_t v___x_1076_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_add(v_i_1072_, v___x_1075_);
v_i_1072_ = v___x_1076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1092_, lean_object* v_as_1093_, lean_object* v_i_1094_, lean_object* v_stop_1095_){
_start:
{
size_t v_i_boxed_1096_; size_t v_stop_boxed_1097_; uint8_t v_res_1098_; lean_object* v_r_1099_; 
v_i_boxed_1096_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_stop_boxed_1097_ = lean_unbox_usize(v_stop_1095_);
lean_dec(v_stop_1095_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1092_, v_as_1093_, v_i_boxed_1096_, v_stop_boxed_1097_);
lean_dec_ref(v_as_1093_);
lean_dec(v_mod_1092_);
v_r_1099_ = lean_box(v_res_1098_);
return v_r_1099_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1100_, lean_object* v_self_1101_){
_start:
{
lean_object* v_targetDecls_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_targetDecls_1102_ = lean_ctor_get(v_self_1101_, 15);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_array_get_size(v_targetDecls_1102_);
v___x_1105_ = lean_nat_dec_lt(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
return v___x_1105_;
}
else
{
if (v___x_1105_ == 0)
{
return v___x_1105_;
}
else
{
size_t v___x_1106_; size_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = ((size_t)0ULL);
v___x_1107_ = lean_usize_of_nat(v___x_1104_);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1100_, v_targetDecls_1102_, v___x_1106_, v___x_1107_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1109_, lean_object* v_self_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lake_Package_isBuildableModule(v_mod_1109_, v_self_1110_);
lean_dec_ref(v_self_1110_);
lean_dec(v_mod_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1113_){
_start:
{
lean_object* v_config_1115_; lean_object* v_dir_1116_; lean_object* v_buildDir_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_config_1115_ = lean_ctor_get(v_self_1113_, 6);
lean_inc_ref(v_config_1115_);
v_dir_1116_ = lean_ctor_get(v_self_1113_, 4);
lean_inc_ref(v_dir_1116_);
lean_dec_ref(v_self_1113_);
v_buildDir_1117_ = lean_ctor_get(v_config_1115_, 5);
lean_inc_ref(v_buildDir_1117_);
lean_dec_ref(v_config_1115_);
v___x_1118_ = l_System_FilePath_normalize(v_buildDir_1117_);
v___x_1119_ = l_Lake_joinRelative(v_dir_1116_, v___x_1118_);
v___x_1120_ = l_Lake_removeDirAllIfExists(v___x_1119_);
lean_dec_ref(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lake_Package_clean(v_self_1121_);
return v_res_1123_;
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Script(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ConfigDecl(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_PackageConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin);
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
res = runtime_initialize_Lake_Config_LakeConfig(builtin);
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
lean_object* initialize_Lake_Config_LakeConfig(uint8_t builtin);
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
res = initialize_Lake_Config_LakeConfig(builtin);
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
