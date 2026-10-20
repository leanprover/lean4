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
lean_object* l_Lake_instInhabitedPackageConfig_default___redArg();
lean_object* l_Lake_OrdHashSet_empty___redArg();
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_198_ = lean_nat_add(v___y_195_, v___y_197_);
lean_dec(v___y_197_);
lean_dec(v___y_195_);
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
lean_ctor_set(v___x_178_, 3, v___y_196_);
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
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___y_196_);
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
v___y_195_ = v___x_210_;
v___y_196_ = v___x_209_;
v___y_197_ = v_size_211_;
goto v___jp_194_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___y_195_ = v___x_210_;
v___y_196_ = v___x_209_;
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
lean_object* v___x_374_; 
v___x_374_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__13, &l_Lake_instInhabitedPackage_default___closed__13_once, _init_l_Lake_instInhabitedPackage_default___closed__13);
v___y_367_ = v___x_374_;
goto v___jp_366_;
}
v___jp_356_:
{
lean_object* v_testDriver_363_; lean_object* v_lintDriver_364_; lean_object* v___x_365_; 
v_testDriver_363_ = lean_ctor_get(v___x_354_, 12);
v_lintDriver_364_ = lean_ctor_get(v___x_354_, 14);
lean_inc_ref(v_lintDriver_364_);
lean_inc_ref(v_testDriver_363_);
lean_inc_ref(v___y_362_);
lean_inc_ref(v___y_360_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
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
lean_ctor_set(v___x_365_, 16, v___y_358_);
lean_ctor_set(v___x_365_, 17, v___y_359_);
lean_ctor_set(v___x_365_, 18, v___y_357_);
lean_ctor_set(v___x_365_, 19, v___y_361_);
lean_ctor_set(v___x_365_, 20, v___y_360_);
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
v___y_357_ = v___x_369_;
v___y_358_ = v___y_367_;
v___y_359_ = v___x_355_;
v___y_360_ = v___x_355_;
v___y_361_ = v___x_355_;
v___y_362_ = v_val_370_;
goto v___jp_356_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__9, &l_Lake_instInhabitedPackage_default___closed__9_once, _init_l_Lake_instInhabitedPackage_default___closed__9);
v___y_357_ = v___x_369_;
v___y_358_ = v___y_367_;
v___y_359_ = v___x_355_;
v___y_360_ = v___x_355_;
v___y_361_ = v___x_355_;
v___y_362_ = v___x_371_;
goto v___jp_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object* v_00_u03b2_375_, lean_object* v_k_376_, lean_object* v_v_377_, lean_object* v_t_378_, lean_object* v_hl_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_376_, v_v_377_, v_t_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lake_instInhabitedPackage_default;
return v___x_381_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_382_){
_start:
{
lean_object* v_keyName_383_; 
v_keyName_383_ = lean_ctor_get(v_pkg_382_, 2);
if (lean_obj_tag(v_keyName_383_) == 0)
{
uint64_t v___x_384_; 
v___x_384_ = 1723ULL;
return v___x_384_;
}
else
{
uint64_t v_hash_385_; 
v_hash_385_ = lean_ctor_get_uint64(v_keyName_383_, sizeof(void*)*2);
return v_hash_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_386_){
_start:
{
uint64_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Lake_Package_instHashable___lam__0(v_pkg_386_);
lean_dec_ref(v_pkg_386_);
v_r_388_ = lean_box_uint64(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_391_, lean_object* v_p2_392_){
_start:
{
lean_object* v_wsIdx_393_; lean_object* v_wsIdx_394_; uint8_t v___x_395_; 
v_wsIdx_393_ = lean_ctor_get(v_p1_391_, 0);
v_wsIdx_394_ = lean_ctor_get(v_p2_392_, 0);
v___x_395_ = lean_nat_dec_eq(v_wsIdx_393_, v_wsIdx_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_396_, lean_object* v_p2_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lake_Package_instBEq___lam__0(v_p1_396_, v_p2_397_);
lean_dec_ref(v_p2_397_);
lean_dec_ref(v_p1_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_402_){
_start:
{
lean_object* v_baseName_403_; uint8_t v___x_404_; lean_object* v___x_405_; 
v_baseName_403_ = lean_ctor_get(v_self_402_, 1);
lean_inc(v_baseName_403_);
lean_dec_ref(v_self_402_);
v___x_404_ = 0;
v___x_405_ = l_Lean_Name_toString(v_baseName_403_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_406_){
_start:
{
lean_object* v_keyName_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_keyName_407_ = lean_ctor_get(v_x_406_, 2);
lean_inc(v_keyName_407_);
lean_dec_ref(v_x_406_);
v___x_408_ = 1;
v___x_409_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_407_, v___x_408_);
v___x_410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_413_){
_start:
{
lean_object* v_baseName_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
v_baseName_414_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_baseName_414_);
lean_dec_ref(v_x_413_);
v___x_415_ = 0;
v___x_416_ = l_Lean_Name_toString(v_baseName_414_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_419_){
_start:
{
lean_object* v_baseName_420_; 
v_baseName_420_ = lean_ctor_get(v_self_419_, 1);
lean_inc(v_baseName_420_);
return v_baseName_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lake_Package_name(v_self_421_);
lean_dec_ref(v_self_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_423_){
_start:
{
lean_object* v_origName_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v_origName_424_ = lean_ctor_get(v_self_423_, 3);
lean_inc(v_origName_424_);
lean_dec_ref(v_self_423_);
v___x_425_ = 0;
v___x_426_ = l_Lean_Name_toString(v_origName_424_, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_unsigned_to_nat(16u);
v___x_429_ = lean_mk_array(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_434_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(lean_object* v_self_436_){
_start:
{
lean_inc_ref(v_self_436_);
return v_self_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed(lean_object* v_self_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(v_self_437_);
lean_dec_ref(v_self_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg(){
_start:
{
lean_object* v___f_441_; 
v___f_441_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___boxed(lean_object* v___dummy_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lake_NPackage_instCoeOutPackage___redArg();
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_444_){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_){
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed(lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(v_x_457_, v___y_458_, v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v_x_457_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg(){
_start:
{
lean_object* v___f_464_; 
v___f_464_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___boxed(lean_object* v___dummy_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lake_instInhabitedPostUpdateHook_default___redArg();
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_467_){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_469_);
lean_dec(v_pkgName_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg(){
_start:
{
lean_object* v___f_472_; 
v___f_472_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg___boxed(lean_object* v___dummy_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lake_instInhabitedPostUpdateHook___redArg();
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_475_){
_start:
{
lean_object* v___f_476_; 
v___f_476_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_instInhabitedPostUpdateHook(v_a_477_);
lean_dec(v_a_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_479_){
_start:
{
lean_inc_ref(v_a_479_);
return v_a_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_480_);
lean_dec_ref(v_a_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_482_, lean_object* v_a_483_){
_start:
{
lean_inc_ref(v_a_483_);
return v_a_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_484_, v_a_485_);
lean_dec_ref(v_a_485_);
lean_dec(v_name_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_488_, 0, v_name_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_489_){
_start:
{
lean_inc(v_a_489_);
return v_a_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_490_);
lean_dec(v_a_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_492_, lean_object* v_a_493_){
_start:
{
lean_inc(v_a_493_);
return v_a_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec(v_name_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_498_, 0, v_name_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_499_){
_start:
{
lean_inc_ref(v_inst_499_);
return v_inst_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_500_);
lean_dec_ref(v_inst_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_502_, lean_object* v_inst_503_){
_start:
{
lean_inc_ref(v_inst_503_);
return v_inst_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_504_, lean_object* v_inst_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_504_, v_inst_505_);
lean_dec_ref(v_inst_505_);
lean_dec(v_name_504_);
return v_res_506_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_514_){
_start:
{
lean_object* v_wsIdx_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_wsIdx_515_ = lean_ctor_get(v_self_514_, 0);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_nat_dec_eq(v_wsIdx_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lake_Package_isRoot(v_self_518_);
lean_dec_ref(v_self_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_521_){
_start:
{
lean_object* v_config_522_; uint8_t v_bootstrap_523_; 
v_config_522_ = lean_ctor_get(v_self_521_, 6);
v_bootstrap_523_ = lean_ctor_get_uint8(v_config_522_, sizeof(void*)*28);
return v_bootstrap_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lake_Package_bootstrap(v_self_524_);
lean_dec_ref(v_self_524_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_527_){
_start:
{
lean_object* v_config_528_; uint8_t v_bootstrap_529_; 
v_config_528_ = lean_ctor_get(v_self_527_, 6);
v_bootstrap_529_ = lean_ctor_get_uint8(v_config_528_, sizeof(void*)*28);
if (v_bootstrap_529_ == 0)
{
lean_object* v_origName_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_origName_530_ = lean_ctor_get(v_self_527_, 3);
lean_inc(v_origName_530_);
lean_dec_ref(v_self_527_);
v___x_531_ = l_Lean_Name_toString(v_origName_530_, v_bootstrap_529_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; 
lean_dec_ref(v_self_527_);
v___x_533_ = lean_box(0);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_534_){
_start:
{
lean_object* v_config_535_; lean_object* v_version_536_; 
v_config_535_ = lean_ctor_get(v_self_534_, 6);
v_version_536_ = lean_ctor_get(v_config_535_, 16);
lean_inc_ref(v_version_536_);
return v_version_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lake_Package_version(v_self_537_);
lean_dec_ref(v_self_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_539_){
_start:
{
lean_object* v_config_540_; lean_object* v_versionTags_541_; 
v_config_540_ = lean_ctor_get(v_self_539_, 6);
v_versionTags_541_ = lean_ctor_get(v_config_540_, 17);
lean_inc_ref(v_versionTags_541_);
return v_versionTags_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lake_Package_versionTags(v_self_542_);
lean_dec_ref(v_self_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_544_){
_start:
{
lean_object* v_config_545_; lean_object* v_description_546_; 
v_config_545_ = lean_ctor_get(v_self_544_, 6);
v_description_546_ = lean_ctor_get(v_config_545_, 18);
lean_inc_ref(v_description_546_);
return v_description_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lake_Package_description(v_self_547_);
lean_dec_ref(v_self_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_549_){
_start:
{
lean_object* v_config_550_; lean_object* v_keywords_551_; 
v_config_550_ = lean_ctor_get(v_self_549_, 6);
v_keywords_551_ = lean_ctor_get(v_config_550_, 19);
lean_inc_ref(v_keywords_551_);
return v_keywords_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lake_Package_keywords(v_self_552_);
lean_dec_ref(v_self_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_554_){
_start:
{
lean_object* v_config_555_; lean_object* v_homepage_556_; 
v_config_555_ = lean_ctor_get(v_self_554_, 6);
v_homepage_556_ = lean_ctor_get(v_config_555_, 20);
lean_inc_ref(v_homepage_556_);
return v_homepage_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lake_Package_homepage(v_self_557_);
lean_dec_ref(v_self_557_);
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_559_){
_start:
{
lean_object* v_config_560_; uint8_t v_reservoir_561_; 
v_config_560_ = lean_ctor_get(v_self_559_, 6);
v_reservoir_561_ = lean_ctor_get_uint8(v_config_560_, sizeof(void*)*28 + 3);
return v_reservoir_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Lake_Package_reservoir(v_self_562_);
lean_dec_ref(v_self_562_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_565_){
_start:
{
lean_object* v_config_566_; lean_object* v_license_567_; 
v_config_566_ = lean_ctor_get(v_self_565_, 6);
v_license_567_ = lean_ctor_get(v_config_566_, 21);
lean_inc_ref(v_license_567_);
return v_license_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_Package_license(v_self_568_);
lean_dec_ref(v_self_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_590_){
_start:
{
lean_object* v_config_591_; lean_object* v_licenseFiles_592_; lean_object* v___f_593_; lean_object* v___x_594_; size_t v_sz_595_; size_t v___x_596_; lean_object* v___x_597_; 
v_config_591_ = lean_ctor_get(v_self_590_, 6);
lean_inc_ref(v_config_591_);
lean_dec_ref(v_self_590_);
v_licenseFiles_592_ = lean_ctor_get(v_config_591_, 22);
lean_inc_ref(v_licenseFiles_592_);
lean_dec_ref(v_config_591_);
v___f_593_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_594_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_595_ = lean_array_size(v_licenseFiles_592_);
v___x_596_ = ((size_t)0ULL);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_594_, v___f_593_, v_sz_595_, v___x_596_, v_licenseFiles_592_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = l_System_FilePath_normalize(v_x_599_);
v___x_601_ = l_Lake_joinRelative(v_dir_598_, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_602_){
_start:
{
lean_object* v_config_603_; lean_object* v_dir_604_; lean_object* v_licenseFiles_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___x_608_; size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; size_t v_sz_612_; lean_object* v___x_613_; 
v_config_603_ = lean_ctor_get(v_self_602_, 6);
lean_inc_ref(v_config_603_);
v_dir_604_ = lean_ctor_get(v_self_602_, 4);
lean_inc_ref(v_dir_604_);
lean_dec_ref(v_self_602_);
v_licenseFiles_605_ = lean_ctor_get(v_config_603_, 22);
lean_inc_ref(v_licenseFiles_605_);
lean_dec_ref(v_config_603_);
v___f_606_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_607_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_607_, 0, v_dir_604_);
v___x_608_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_609_ = lean_array_size(v_licenseFiles_605_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_608_, v___f_606_, v_sz_609_, v___x_610_, v_licenseFiles_605_);
v_sz_612_ = lean_array_size(v___x_611_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_608_, v___f_607_, v_sz_612_, v___x_610_, v___x_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_614_){
_start:
{
lean_object* v_config_615_; lean_object* v_readmeFile_616_; lean_object* v___x_617_; 
v_config_615_ = lean_ctor_get(v_self_614_, 6);
lean_inc_ref(v_config_615_);
lean_dec_ref(v_self_614_);
v_readmeFile_616_ = lean_ctor_get(v_config_615_, 23);
lean_inc_ref(v_readmeFile_616_);
lean_dec_ref(v_config_615_);
v___x_617_ = l_System_FilePath_normalize(v_readmeFile_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_618_){
_start:
{
lean_object* v_config_619_; lean_object* v_dir_620_; lean_object* v_readmeFile_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_config_619_ = lean_ctor_get(v_self_618_, 6);
lean_inc_ref(v_config_619_);
v_dir_620_ = lean_ctor_get(v_self_618_, 4);
lean_inc_ref(v_dir_620_);
lean_dec_ref(v_self_618_);
v_readmeFile_621_ = lean_ctor_get(v_config_619_, 23);
lean_inc_ref(v_readmeFile_621_);
lean_dec_ref(v_config_619_);
v___x_622_ = l_System_FilePath_normalize(v_readmeFile_621_);
v___x_623_ = l_Lake_joinRelative(v_dir_620_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg(){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lake_defaultLakeDir;
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg___boxed(lean_object* v___dummy_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lake_Package_relLakeDir___redArg();
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lake_defaultLakeDir;
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lake_Package_relLakeDir(v_x_630_);
lean_dec_ref(v_x_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_632_){
_start:
{
lean_object* v_dir_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_dir_633_ = lean_ctor_get(v_self_632_, 4);
lean_inc_ref(v_dir_633_);
lean_dec_ref(v_self_632_);
v___x_634_ = l_Lake_defaultLakeDir;
v___x_635_ = l_Lake_joinRelative(v_dir_633_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_636_){
_start:
{
lean_object* v_config_637_; lean_object* v_toWorkspaceConfig_638_; lean_object* v___x_639_; 
v_config_637_ = lean_ctor_get(v_self_636_, 6);
lean_inc_ref(v_config_637_);
lean_dec_ref(v_self_636_);
v_toWorkspaceConfig_638_ = lean_ctor_get(v_config_637_, 0);
lean_inc_ref(v_toWorkspaceConfig_638_);
lean_dec_ref(v_config_637_);
v___x_639_ = l_System_FilePath_normalize(v_toWorkspaceConfig_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_640_){
_start:
{
lean_object* v_config_641_; lean_object* v_dir_642_; lean_object* v_toWorkspaceConfig_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_config_641_ = lean_ctor_get(v_self_640_, 6);
lean_inc_ref(v_config_641_);
v_dir_642_ = lean_ctor_get(v_self_640_, 4);
lean_inc_ref(v_dir_642_);
lean_dec_ref(v_self_640_);
v_toWorkspaceConfig_643_ = lean_ctor_get(v_config_641_, 0);
lean_inc_ref(v_toWorkspaceConfig_643_);
lean_dec_ref(v_config_641_);
v___x_644_ = l_System_FilePath_normalize(v_toWorkspaceConfig_643_);
v___x_645_ = l_Lake_joinRelative(v_dir_642_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_646_){
_start:
{
lean_object* v_dir_647_; lean_object* v_relManifestFile_648_; lean_object* v___x_649_; 
v_dir_647_ = lean_ctor_get(v_self_646_, 4);
lean_inc_ref(v_dir_647_);
v_relManifestFile_648_ = lean_ctor_get(v_self_646_, 9);
lean_inc_ref(v_relManifestFile_648_);
lean_dec_ref(v_self_646_);
v___x_649_ = l_Lake_joinRelative(v_dir_647_, v_relManifestFile_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_650_){
_start:
{
lean_object* v_config_651_; lean_object* v_dir_652_; lean_object* v_buildDir_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_config_651_ = lean_ctor_get(v_self_650_, 6);
lean_inc_ref(v_config_651_);
v_dir_652_ = lean_ctor_get(v_self_650_, 4);
lean_inc_ref(v_dir_652_);
lean_dec_ref(v_self_650_);
v_buildDir_653_ = lean_ctor_get(v_config_651_, 5);
lean_inc_ref(v_buildDir_653_);
lean_dec_ref(v_config_651_);
v___x_654_ = l_System_FilePath_normalize(v_buildDir_653_);
v___x_655_ = l_Lake_joinRelative(v_dir_652_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_656_){
_start:
{
lean_object* v_config_657_; lean_object* v_testDriverArgs_658_; 
v_config_657_ = lean_ctor_get(v_self_656_, 6);
v_testDriverArgs_658_ = lean_ctor_get(v_config_657_, 13);
lean_inc_ref(v_testDriverArgs_658_);
return v_testDriverArgs_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lake_Package_testDriverArgs(v_self_659_);
lean_dec_ref(v_self_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_661_){
_start:
{
lean_object* v_config_662_; lean_object* v_lintDriverArgs_663_; 
v_config_662_ = lean_ctor_get(v_self_661_, 6);
v_lintDriverArgs_663_ = lean_ctor_get(v_config_662_, 15);
lean_inc_ref(v_lintDriverArgs_663_);
return v_lintDriverArgs_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lake_Package_lintDriverArgs(v_self_664_);
lean_dec_ref(v_self_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_666_){
_start:
{
lean_object* v_config_667_; lean_object* v_extraDepTargets_668_; 
v_config_667_ = lean_ctor_get(v_self_666_, 6);
v_extraDepTargets_668_ = lean_ctor_get(v_config_667_, 2);
lean_inc_ref(v_extraDepTargets_668_);
return v_extraDepTargets_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lake_Package_extraDepTargets(v_self_669_);
lean_dec_ref(v_self_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_671_){
_start:
{
lean_object* v_config_672_; lean_object* v_toLeanConfig_673_; lean_object* v_platformIndependent_674_; 
v_config_672_ = lean_ctor_get(v_self_671_, 6);
v_toLeanConfig_673_ = lean_ctor_get(v_config_672_, 1);
v_platformIndependent_674_ = lean_ctor_get(v_toLeanConfig_673_, 10);
lean_inc(v_platformIndependent_674_);
return v_platformIndependent_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_Package_platformIndependent(v_self_675_);
lean_dec_ref(v_self_675_);
return v_res_676_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_683_){
_start:
{
lean_object* v_config_684_; lean_object* v_toLeanConfig_685_; lean_object* v_platformIndependent_686_; lean_object* v___f_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_config_684_ = lean_ctor_get(v_self_683_, 6);
lean_inc_ref(v_config_684_);
lean_dec_ref(v_self_683_);
v_toLeanConfig_685_ = lean_ctor_get(v_config_684_, 1);
lean_inc_ref(v_toLeanConfig_685_);
lean_dec_ref(v_config_684_);
v_platformIndependent_686_ = lean_ctor_get(v_toLeanConfig_685_, 10);
lean_inc(v_platformIndependent_686_);
lean_dec_ref(v_toLeanConfig_685_);
v___f_687_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_688_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_689_ = l_instBEqOption_beq___redArg(v___f_687_, v_platformIndependent_686_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lake_Package_isPlatformIndependent(v_self_690_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_693_){
_start:
{
lean_object* v_config_694_; uint8_t v_fixedToolchain_695_; 
v_config_694_ = lean_ctor_get(v_self_693_, 6);
v_fixedToolchain_695_ = lean_ctor_get_uint8(v_config_694_, sizeof(void*)*28 + 6);
return v_fixedToolchain_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lake_Package_fixedToolchain(v_self_696_);
lean_dec_ref(v_self_696_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_699_){
_start:
{
lean_object* v_config_700_; lean_object* v_releaseRepo_701_; 
v_config_700_ = lean_ctor_get(v_self_699_, 6);
v_releaseRepo_701_ = lean_ctor_get(v_config_700_, 10);
lean_inc(v_releaseRepo_701_);
return v_releaseRepo_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lake_Package_releaseRepo_x3f(v_self_702_);
lean_dec_ref(v_self_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_704_){
_start:
{
lean_object* v_remoteUrl_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_remoteUrl_705_ = lean_ctor_get(v_self_704_, 11);
v___x_706_ = lean_string_utf8_byte_size(v_remoteUrl_705_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_inc_ref(v_remoteUrl_705_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v_remoteUrl_705_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lake_Package_remoteUrl_x3f(v_self_711_);
lean_dec_ref(v_self_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_713_){
_start:
{
lean_object* v_dir_714_; lean_object* v_buildArchive_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_dir_714_ = lean_ctor_get(v_self_713_, 4);
lean_inc_ref(v_dir_714_);
v_buildArchive_715_ = lean_ctor_get(v_self_713_, 21);
lean_inc_ref(v_buildArchive_715_);
lean_dec_ref(v_self_713_);
v___x_716_ = l_Lake_defaultLakeDir;
v___x_717_ = l_Lake_joinRelative(v_dir_714_, v___x_716_);
v___x_718_ = l_Lake_joinRelative(v___x_717_, v_buildArchive_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_720_){
_start:
{
lean_object* v_dir_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_dir_721_ = lean_ctor_get(v_self_720_, 4);
lean_inc_ref(v_dir_721_);
lean_dec_ref(v_self_720_);
v___x_722_ = l_Lake_defaultLakeDir;
v___x_723_ = l_Lake_joinRelative(v_dir_721_, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_725_ = l_Lake_joinRelative(v___x_723_, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_726_){
_start:
{
lean_object* v_config_727_; uint8_t v_preferReleaseBuild_728_; 
v_config_727_ = lean_ctor_get(v_self_726_, 6);
v_preferReleaseBuild_728_ = lean_ctor_get_uint8(v_config_727_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Lake_Package_preferReleaseBuild(v_self_729_);
lean_dec_ref(v_self_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_732_){
_start:
{
lean_object* v_config_733_; uint8_t v_precompileModules_734_; 
v_config_733_ = lean_ctor_get(v_self_732_, 6);
v_precompileModules_734_ = lean_ctor_get_uint8(v_config_733_, sizeof(void*)*28 + 1);
return v_precompileModules_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Lake_Package_precompileModules(v_self_735_);
lean_dec_ref(v_self_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileImports(lean_object* v_self_738_){
_start:
{
lean_object* v_config_739_; lean_object* v_toLeanConfig_740_; uint8_t v_precompileImports_741_; 
v_config_739_ = lean_ctor_get(v_self_738_, 6);
v_toLeanConfig_740_ = lean_ctor_get(v_config_739_, 1);
v_precompileImports_741_ = lean_ctor_get_uint8(v_toLeanConfig_740_, sizeof(void*)*13 + 2);
return v_precompileImports_741_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileImports___boxed(lean_object* v_self_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_Lake_Package_precompileImports(v_self_742_);
lean_dec_ref(v_self_742_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_745_){
_start:
{
lean_object* v_config_746_; lean_object* v_moreGlobalServerArgs_747_; 
v_config_746_ = lean_ctor_get(v_self_745_, 6);
v_moreGlobalServerArgs_747_ = lean_ctor_get(v_config_746_, 3);
lean_inc_ref(v_moreGlobalServerArgs_747_);
return v_moreGlobalServerArgs_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lake_Package_moreGlobalServerArgs(v_self_748_);
lean_dec_ref(v_self_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_750_){
_start:
{
lean_object* v_config_751_; lean_object* v_toLeanConfig_752_; lean_object* v_leanOptions_753_; lean_object* v_moreServerOptions_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_config_751_ = lean_ctor_get(v_self_750_, 6);
v_toLeanConfig_752_ = lean_ctor_get(v_config_751_, 1);
v_leanOptions_753_ = lean_ctor_get(v_toLeanConfig_752_, 0);
v_moreServerOptions_754_ = lean_ctor_get(v_toLeanConfig_752_, 4);
v___x_755_ = l_Lean_LeanOptions_ofArray(v_leanOptions_753_);
v___x_756_ = l_Lean_LeanOptions_appendArray(v___x_755_, v_moreServerOptions_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lake_Package_moreServerOptions(v_self_757_);
lean_dec_ref(v_self_757_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_759_){
_start:
{
lean_object* v_config_760_; lean_object* v_toLeanConfig_761_; uint8_t v_buildType_762_; 
v_config_760_ = lean_ctor_get(v_self_759_, 6);
v_toLeanConfig_761_ = lean_ctor_get(v_config_760_, 1);
v_buildType_762_ = lean_ctor_get_uint8(v_toLeanConfig_761_, sizeof(void*)*13);
return v_buildType_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lake_Package_buildType(v_self_763_);
lean_dec_ref(v_self_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_766_){
_start:
{
lean_object* v_config_767_; lean_object* v_toLeanConfig_768_; uint8_t v_backend_769_; 
v_config_767_ = lean_ctor_get(v_self_766_, 6);
v_toLeanConfig_768_ = lean_ctor_get(v_config_767_, 1);
v_backend_769_ = lean_ctor_get_uint8(v_toLeanConfig_768_, sizeof(void*)*13 + 1);
return v_backend_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lake_Package_backend(v_self_770_);
lean_dec_ref(v_self_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_773_){
_start:
{
lean_object* v_config_774_; uint8_t v_allowImportAll_775_; 
v_config_774_ = lean_ctor_get(v_self_773_, 6);
v_allowImportAll_775_ = lean_ctor_get_uint8(v_config_774_, sizeof(void*)*28 + 5);
return v_allowImportAll_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Lake_Package_allowImportAll(v_self_776_);
lean_dec_ref(v_self_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_779_){
_start:
{
lean_object* v_config_780_; lean_object* v_toLeanConfig_781_; uint8_t v_requiresModuleSystem_782_; 
v_config_780_ = lean_ctor_get(v_self_779_, 6);
v_toLeanConfig_781_ = lean_ctor_get(v_config_780_, 1);
v_requiresModuleSystem_782_ = lean_ctor_get_uint8(v_toLeanConfig_781_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lake_Package_requiresModuleSystem(v_self_783_);
lean_dec_ref(v_self_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_786_){
_start:
{
lean_object* v_config_787_; lean_object* v_toLeanConfig_788_; uint8_t v_allowNonModules_789_; 
v_config_787_ = lean_ctor_get(v_self_786_, 6);
v_toLeanConfig_788_ = lean_ctor_get(v_config_787_, 1);
v_allowNonModules_789_ = lean_ctor_get_uint8(v_toLeanConfig_788_, sizeof(void*)*13 + 4);
return v_allowNonModules_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Lake_Package_allowNonModules(v_self_790_);
lean_dec_ref(v_self_790_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_793_){
_start:
{
lean_object* v_config_794_; lean_object* v_toLeanConfig_795_; lean_object* v_dynlibs_796_; 
v_config_794_ = lean_ctor_get(v_self_793_, 6);
v_toLeanConfig_795_ = lean_ctor_get(v_config_794_, 1);
v_dynlibs_796_ = lean_ctor_get(v_toLeanConfig_795_, 11);
lean_inc_ref(v_dynlibs_796_);
return v_dynlibs_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_Package_dynlibs(v_self_797_);
lean_dec_ref(v_self_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_799_){
_start:
{
lean_object* v_config_800_; lean_object* v_toLeanConfig_801_; lean_object* v_plugins_802_; 
v_config_800_ = lean_ctor_get(v_self_799_, 6);
v_toLeanConfig_801_ = lean_ctor_get(v_config_800_, 1);
v_plugins_802_ = lean_ctor_get(v_toLeanConfig_801_, 12);
lean_inc_ref(v_plugins_802_);
return v_plugins_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lake_Package_plugins(v_self_803_);
lean_dec_ref(v_self_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_805_){
_start:
{
lean_object* v_config_806_; lean_object* v_toLeanConfig_807_; lean_object* v_leanOptions_808_; lean_object* v___x_809_; 
v_config_806_ = lean_ctor_get(v_self_805_, 6);
v_toLeanConfig_807_ = lean_ctor_get(v_config_806_, 1);
v_leanOptions_808_ = lean_ctor_get(v_toLeanConfig_807_, 0);
v___x_809_ = l_Lean_LeanOptions_ofArray(v_leanOptions_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lake_Package_leanOptions(v_self_810_);
lean_dec_ref(v_self_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_812_){
_start:
{
lean_object* v_config_813_; lean_object* v_toLeanConfig_814_; lean_object* v_moreLeanArgs_815_; 
v_config_813_ = lean_ctor_get(v_self_812_, 6);
v_toLeanConfig_814_ = lean_ctor_get(v_config_813_, 1);
v_moreLeanArgs_815_ = lean_ctor_get(v_toLeanConfig_814_, 1);
lean_inc_ref(v_moreLeanArgs_815_);
return v_moreLeanArgs_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_Package_moreLeanArgs(v_self_816_);
lean_dec_ref(v_self_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_818_){
_start:
{
lean_object* v_config_819_; lean_object* v_toLeanConfig_820_; lean_object* v_weakLeanArgs_821_; 
v_config_819_ = lean_ctor_get(v_self_818_, 6);
v_toLeanConfig_820_ = lean_ctor_get(v_config_819_, 1);
v_weakLeanArgs_821_ = lean_ctor_get(v_toLeanConfig_820_, 2);
lean_inc_ref(v_weakLeanArgs_821_);
return v_weakLeanArgs_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lake_Package_weakLeanArgs(v_self_822_);
lean_dec_ref(v_self_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_824_){
_start:
{
lean_object* v_config_825_; lean_object* v_toLeanConfig_826_; lean_object* v_moreLeancArgs_827_; 
v_config_825_ = lean_ctor_get(v_self_824_, 6);
v_toLeanConfig_826_ = lean_ctor_get(v_config_825_, 1);
v_moreLeancArgs_827_ = lean_ctor_get(v_toLeanConfig_826_, 3);
lean_inc_ref(v_moreLeancArgs_827_);
return v_moreLeancArgs_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_Package_moreLeancArgs(v_self_828_);
lean_dec_ref(v_self_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_830_){
_start:
{
lean_object* v_config_831_; lean_object* v_toLeanConfig_832_; lean_object* v_weakLeancArgs_833_; 
v_config_831_ = lean_ctor_get(v_self_830_, 6);
v_toLeanConfig_832_ = lean_ctor_get(v_config_831_, 1);
v_weakLeancArgs_833_ = lean_ctor_get(v_toLeanConfig_832_, 5);
lean_inc_ref(v_weakLeancArgs_833_);
return v_weakLeancArgs_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_Package_weakLeancArgs(v_self_834_);
lean_dec_ref(v_self_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_836_){
_start:
{
lean_object* v_config_837_; lean_object* v_toLeanConfig_838_; lean_object* v_moreLinkObjs_839_; 
v_config_837_ = lean_ctor_get(v_self_836_, 6);
v_toLeanConfig_838_ = lean_ctor_get(v_config_837_, 1);
v_moreLinkObjs_839_ = lean_ctor_get(v_toLeanConfig_838_, 6);
lean_inc_ref(v_moreLinkObjs_839_);
return v_moreLinkObjs_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lake_Package_moreLinkObjs(v_self_840_);
lean_dec_ref(v_self_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_842_){
_start:
{
lean_object* v_config_843_; lean_object* v_toLeanConfig_844_; lean_object* v_moreLinkLibs_845_; 
v_config_843_ = lean_ctor_get(v_self_842_, 6);
v_toLeanConfig_844_ = lean_ctor_get(v_config_843_, 1);
v_moreLinkLibs_845_ = lean_ctor_get(v_toLeanConfig_844_, 7);
lean_inc_ref(v_moreLinkLibs_845_);
return v_moreLinkLibs_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_Package_moreLinkLibs(v_self_846_);
lean_dec_ref(v_self_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_848_){
_start:
{
lean_object* v_config_849_; lean_object* v_toLeanConfig_850_; lean_object* v_moreLinkArgs_851_; 
v_config_849_ = lean_ctor_get(v_self_848_, 6);
v_toLeanConfig_850_ = lean_ctor_get(v_config_849_, 1);
v_moreLinkArgs_851_ = lean_ctor_get(v_toLeanConfig_850_, 8);
lean_inc_ref(v_moreLinkArgs_851_);
return v_moreLinkArgs_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lake_Package_moreLinkArgs(v_self_852_);
lean_dec_ref(v_self_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_854_){
_start:
{
lean_object* v_config_855_; lean_object* v_toLeanConfig_856_; lean_object* v_weakLinkArgs_857_; 
v_config_855_ = lean_ctor_get(v_self_854_, 6);
v_toLeanConfig_856_ = lean_ctor_get(v_config_855_, 1);
v_weakLinkArgs_857_ = lean_ctor_get(v_toLeanConfig_856_, 9);
lean_inc_ref(v_weakLinkArgs_857_);
return v_weakLinkArgs_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_Package_weakLinkArgs(v_self_858_);
lean_dec_ref(v_self_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_860_){
_start:
{
lean_object* v_config_861_; lean_object* v_dir_862_; lean_object* v_srcDir_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_config_861_ = lean_ctor_get(v_self_860_, 6);
lean_inc_ref(v_config_861_);
v_dir_862_ = lean_ctor_get(v_self_860_, 4);
lean_inc_ref(v_dir_862_);
lean_dec_ref(v_self_860_);
v_srcDir_863_ = lean_ctor_get(v_config_861_, 4);
lean_inc_ref(v_srcDir_863_);
lean_dec_ref(v_config_861_);
v___x_864_ = l_System_FilePath_normalize(v_srcDir_863_);
v___x_865_ = l_Lake_joinRelative(v_dir_862_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_866_){
_start:
{
lean_object* v_config_867_; lean_object* v_dir_868_; lean_object* v_srcDir_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_config_867_ = lean_ctor_get(v_self_866_, 6);
lean_inc_ref(v_config_867_);
v_dir_868_ = lean_ctor_get(v_self_866_, 4);
lean_inc_ref(v_dir_868_);
lean_dec_ref(v_self_866_);
v_srcDir_869_ = lean_ctor_get(v_config_867_, 4);
lean_inc_ref(v_srcDir_869_);
lean_dec_ref(v_config_867_);
v___x_870_ = l_System_FilePath_normalize(v_srcDir_869_);
v___x_871_ = l_Lake_joinRelative(v_dir_868_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_872_){
_start:
{
lean_object* v_config_873_; lean_object* v_dir_874_; lean_object* v_buildDir_875_; lean_object* v_leanLibDir_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_config_873_ = lean_ctor_get(v_self_872_, 6);
lean_inc_ref(v_config_873_);
v_dir_874_ = lean_ctor_get(v_self_872_, 4);
lean_inc_ref(v_dir_874_);
lean_dec_ref(v_self_872_);
v_buildDir_875_ = lean_ctor_get(v_config_873_, 5);
lean_inc_ref(v_buildDir_875_);
v_leanLibDir_876_ = lean_ctor_get(v_config_873_, 6);
lean_inc_ref(v_leanLibDir_876_);
lean_dec_ref(v_config_873_);
v___x_877_ = l_System_FilePath_normalize(v_buildDir_875_);
v___x_878_ = l_Lake_joinRelative(v_dir_874_, v___x_877_);
v___x_879_ = l_System_FilePath_normalize(v_leanLibDir_876_);
v___x_880_ = l_Lake_joinRelative(v___x_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object* v_self_882_){
_start:
{
lean_object* v_config_883_; lean_object* v_dir_884_; lean_object* v_buildDir_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_config_883_ = lean_ctor_get(v_self_882_, 6);
lean_inc_ref(v_config_883_);
v_dir_884_ = lean_ctor_get(v_self_882_, 4);
lean_inc_ref(v_dir_884_);
lean_dec_ref(v_self_882_);
v_buildDir_885_ = lean_ctor_get(v_config_883_, 5);
lean_inc_ref(v_buildDir_885_);
lean_dec_ref(v_config_883_);
v___x_886_ = l_System_FilePath_normalize(v_buildDir_885_);
v___x_887_ = l_Lake_joinRelative(v_dir_884_, v___x_886_);
v___x_888_ = ((lean_object*)(l_Lake_Package_bootstrapIncludeDir___closed__0));
v___x_889_ = l_Lake_joinRelative(v___x_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_890_){
_start:
{
lean_object* v_config_891_; lean_object* v_dir_892_; lean_object* v_buildDir_893_; lean_object* v_nativeLibDir_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_config_891_ = lean_ctor_get(v_self_890_, 6);
lean_inc_ref(v_config_891_);
v_dir_892_ = lean_ctor_get(v_self_890_, 4);
lean_inc_ref(v_dir_892_);
lean_dec_ref(v_self_890_);
v_buildDir_893_ = lean_ctor_get(v_config_891_, 5);
lean_inc_ref(v_buildDir_893_);
v_nativeLibDir_894_ = lean_ctor_get(v_config_891_, 7);
lean_inc_ref(v_nativeLibDir_894_);
lean_dec_ref(v_config_891_);
v___x_895_ = l_System_FilePath_normalize(v_buildDir_893_);
v___x_896_ = l_Lake_joinRelative(v_dir_892_, v___x_895_);
v___x_897_ = l_System_FilePath_normalize(v_nativeLibDir_894_);
v___x_898_ = l_Lake_joinRelative(v___x_896_, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_899_){
_start:
{
lean_object* v_config_900_; lean_object* v_dir_901_; lean_object* v_buildDir_902_; lean_object* v_nativeLibDir_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_config_900_ = lean_ctor_get(v_self_899_, 6);
lean_inc_ref(v_config_900_);
v_dir_901_ = lean_ctor_get(v_self_899_, 4);
lean_inc_ref(v_dir_901_);
lean_dec_ref(v_self_899_);
v_buildDir_902_ = lean_ctor_get(v_config_900_, 5);
lean_inc_ref(v_buildDir_902_);
v_nativeLibDir_903_ = lean_ctor_get(v_config_900_, 7);
lean_inc_ref(v_nativeLibDir_903_);
lean_dec_ref(v_config_900_);
v___x_904_ = l_System_FilePath_normalize(v_buildDir_902_);
v___x_905_ = l_Lake_joinRelative(v_dir_901_, v___x_904_);
v___x_906_ = l_System_FilePath_normalize(v_nativeLibDir_903_);
v___x_907_ = l_Lake_joinRelative(v___x_905_, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_908_){
_start:
{
lean_object* v_config_909_; lean_object* v_dir_910_; lean_object* v_buildDir_911_; lean_object* v_binDir_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_config_909_ = lean_ctor_get(v_self_908_, 6);
lean_inc_ref(v_config_909_);
v_dir_910_ = lean_ctor_get(v_self_908_, 4);
lean_inc_ref(v_dir_910_);
lean_dec_ref(v_self_908_);
v_buildDir_911_ = lean_ctor_get(v_config_909_, 5);
lean_inc_ref(v_buildDir_911_);
v_binDir_912_ = lean_ctor_get(v_config_909_, 8);
lean_inc_ref(v_binDir_912_);
lean_dec_ref(v_config_909_);
v___x_913_ = l_System_FilePath_normalize(v_buildDir_911_);
v___x_914_ = l_Lake_joinRelative(v_dir_910_, v___x_913_);
v___x_915_ = l_System_FilePath_normalize(v_binDir_912_);
v___x_916_ = l_Lake_joinRelative(v___x_914_, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_917_){
_start:
{
lean_object* v_config_918_; lean_object* v_dir_919_; lean_object* v_buildDir_920_; lean_object* v_irDir_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_config_918_ = lean_ctor_get(v_self_917_, 6);
lean_inc_ref(v_config_918_);
v_dir_919_ = lean_ctor_get(v_self_917_, 4);
lean_inc_ref(v_dir_919_);
lean_dec_ref(v_self_917_);
v_buildDir_920_ = lean_ctor_get(v_config_918_, 5);
lean_inc_ref(v_buildDir_920_);
v_irDir_921_ = lean_ctor_get(v_config_918_, 9);
lean_inc_ref(v_irDir_921_);
lean_dec_ref(v_config_918_);
v___x_922_ = l_System_FilePath_normalize(v_buildDir_920_);
v___x_923_ = l_Lake_joinRelative(v_dir_919_, v___x_922_);
v___x_924_ = l_System_FilePath_normalize(v_irDir_921_);
v___x_925_ = l_Lake_joinRelative(v___x_923_, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_926_){
_start:
{
lean_object* v_config_927_; uint8_t v_libPrefixOnWindows_928_; 
v_config_927_ = lean_ctor_get(v_self_926_, 6);
v_libPrefixOnWindows_928_ = lean_ctor_get_uint8(v_config_927_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_929_){
_start:
{
uint8_t v_res_930_; lean_object* v_r_931_; 
v_res_930_ = l_Lake_Package_libPrefixOnWindows(v_self_929_);
lean_dec_ref(v_self_929_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_932_){
_start:
{
lean_object* v_config_933_; lean_object* v_enableArtifactCache_x3f_934_; 
v_config_933_ = lean_ctor_get(v_self_932_, 6);
v_enableArtifactCache_x3f_934_ = lean_ctor_get(v_config_933_, 24);
lean_inc(v_enableArtifactCache_x3f_934_);
return v_enableArtifactCache_x3f_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lake_Package_enableArtifactCache_x3f(v_self_935_);
lean_dec_ref(v_self_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_937_){
_start:
{
lean_object* v_config_938_; lean_object* v_restoreAllArtifacts_x3f_939_; 
v_config_938_ = lean_ctor_get(v_self_937_, 6);
v_restoreAllArtifacts_x3f_939_ = lean_ctor_get(v_config_938_, 25);
lean_inc(v_restoreAllArtifacts_x3f_939_);
return v_restoreAllArtifacts_x3f_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_940_);
lean_dec_ref(v_self_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_942_){
_start:
{
lean_object* v_baseName_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_baseName_943_ = lean_ctor_get(v_self_942_, 1);
lean_inc(v_baseName_943_);
lean_dec_ref(v_self_942_);
v___x_944_ = 0;
v___x_945_ = l_Lean_Name_toString(v_baseName_943_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_947_){
_start:
{
lean_object* v_origName_948_; lean_object* v_scope_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_origName_948_ = lean_ctor_get(v_self_947_, 3);
lean_inc(v_origName_948_);
v_scope_949_ = lean_ctor_get(v_self_947_, 10);
lean_inc_ref(v_scope_949_);
lean_dec_ref(v_self_947_);
v___x_950_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_951_ = lean_string_append(v_scope_949_, v___x_950_);
v___x_952_ = 0;
v___x_953_ = l_Lean_Name_toString(v_origName_948_, v___x_952_);
v___x_954_ = lean_string_append(v___x_951_, v___x_953_);
lean_dec_ref(v___x_953_);
v___x_955_ = l_Lake_CacheServiceScope_ofString(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_956_){
_start:
{
lean_object* v_scope_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_scope_957_ = lean_ctor_get(v_self_956_, 10);
v___x_958_ = lean_string_utf8_byte_size(v_scope_957_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_956_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v_self_956_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_964_, lean_object* v_k_965_){
_start:
{
if (lean_obj_tag(v_t_964_) == 0)
{
lean_object* v_k_966_; lean_object* v_v_967_; lean_object* v_l_968_; lean_object* v_r_969_; uint8_t v___x_970_; 
v_k_966_ = lean_ctor_get(v_t_964_, 1);
v_v_967_ = lean_ctor_get(v_t_964_, 2);
v_l_968_ = lean_ctor_get(v_t_964_, 3);
v_r_969_ = lean_ctor_get(v_t_964_, 4);
v___x_970_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_965_, v_k_966_);
switch(v___x_970_)
{
case 0:
{
v_t_964_ = v_l_968_;
goto _start;
}
case 1:
{
lean_object* v___x_972_; 
lean_inc(v_v_967_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_v_967_);
return v___x_972_;
}
default: 
{
v_t_964_ = v_r_969_;
goto _start;
}
}
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_box(0);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_975_, lean_object* v_k_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_975_, v_k_976_);
lean_dec(v_k_976_);
lean_dec(v_t_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_978_, lean_object* v_self_979_){
_start:
{
lean_object* v_targetDeclMap_980_; lean_object* v___x_981_; 
v_targetDeclMap_980_ = lean_ctor_get(v_self_979_, 16);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_980_, v_name_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_982_, lean_object* v_self_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_Package_findTargetDecl_x3f(v_name_982_, v_self_983_);
lean_dec_ref(v_self_983_);
lean_dec(v_name_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_985_, lean_object* v_inst_986_, lean_object* v_t_987_, lean_object* v_k_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_987_, v_k_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_990_, lean_object* v_inst_991_, lean_object* v_t_992_, lean_object* v_k_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_990_, v_inst_991_, v_t_992_, v_k_993_);
lean_dec(v_k_993_);
lean_dec(v_t_992_);
return v_res_994_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_998_, lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v_kind_1008_; lean_object* v_config_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_999_, v_i_1000_);
v_kind_1008_ = lean_ctor_get(v___x_1007_, 2);
v_config_1009_ = lean_ctor_get(v___x_1007_, 3);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1011_ = lean_name_eq(v_kind_1008_, v___x_1010_);
if (v___x_1011_ == 0)
{
goto v___jp_1002_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_998_, v_config_1009_);
if (v___x_1012_ == 0)
{
goto v___jp_1002_;
}
else
{
return v___x_1012_;
}
}
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = 0;
return v___x_1013_;
}
v___jp_1002_:
{
size_t v___x_1003_; size_t v___x_1004_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_1000_, v___x_1003_);
v_i_1000_ = v___x_1004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_){
_start:
{
size_t v_i_boxed_1018_; size_t v_stop_boxed_1019_; uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_i_boxed_1018_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1014_, v_as_1015_, v_i_boxed_1018_, v_stop_boxed_1019_);
lean_dec_ref(v_as_1015_);
lean_dec(v_mod_1014_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_1022_, lean_object* v_self_1023_){
_start:
{
lean_object* v_targetDecls_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_targetDecls_1024_ = lean_ctor_get(v_self_1023_, 15);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_array_get_size(v_targetDecls_1024_);
v___x_1027_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
return v___x_1027_;
}
else
{
if (v___x_1027_ == 0)
{
return v___x_1027_;
}
else
{
size_t v___x_1028_; size_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1026_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1022_, v_targetDecls_1024_, v___x_1028_, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1031_, lean_object* v_self_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lake_Package_isLocalModule(v_mod_1031_, v_self_1032_);
lean_dec_ref(v_self_1032_);
lean_dec(v_mod_1031_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1035_, lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_kind_1045_; lean_object* v_config_1046_; uint8_t v___x_1047_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1044_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v_kind_1045_ = lean_ctor_get(v___x_1044_, 2);
v_config_1046_ = lean_ctor_get(v___x_1044_, 3);
v___x_1047_ = 1;
v___x_1053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1054_ = lean_name_eq(v_kind_1045_, v___x_1053_);
if (v___x_1054_ == 0)
{
goto v___jp_1048_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1035_, v_config_1046_);
if (v___x_1055_ == 0)
{
goto v___jp_1048_;
}
else
{
return v___x_1047_;
}
}
v___jp_1048_:
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = l_Lake_LeanExe_keyword;
v___x_1050_ = lean_name_eq(v_kind_1045_, v___x_1049_);
if (v___x_1050_ == 0)
{
goto v___jp_1039_;
}
else
{
lean_object* v_root_1051_; uint8_t v___x_1052_; 
v_root_1051_ = lean_ctor_get(v_config_1046_, 2);
v___x_1052_ = lean_name_eq(v_root_1051_, v_mod_1035_);
if (v___x_1052_ == 0)
{
goto v___jp_1039_;
}
else
{
return v___x_1047_;
}
}
}
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = 0;
return v___x_1056_;
}
v___jp_1039_:
{
size_t v___x_1040_; size_t v___x_1041_; 
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1037_, v___x_1040_);
v_i_1037_ = v___x_1041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1057_, lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_stop_1060_){
_start:
{
size_t v_i_boxed_1061_; size_t v_stop_boxed_1062_; uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_i_boxed_1061_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_stop_boxed_1062_ = lean_unbox_usize(v_stop_1060_);
lean_dec(v_stop_1060_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1057_, v_as_1058_, v_i_boxed_1061_, v_stop_boxed_1062_);
lean_dec_ref(v_as_1058_);
lean_dec(v_mod_1057_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1065_, lean_object* v_self_1066_){
_start:
{
lean_object* v_targetDecls_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_targetDecls_1067_ = lean_ctor_get(v_self_1066_, 15);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_array_get_size(v_targetDecls_1067_);
v___x_1070_ = lean_nat_dec_lt(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = lean_usize_of_nat(v___x_1069_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1065_, v_targetDecls_1067_, v___x_1071_, v___x_1072_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1074_, lean_object* v_self_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Lake_Package_isBuildableModule(v_mod_1074_, v_self_1075_);
lean_dec_ref(v_self_1075_);
lean_dec(v_mod_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1078_){
_start:
{
lean_object* v_config_1080_; lean_object* v_dir_1081_; lean_object* v_buildDir_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_config_1080_ = lean_ctor_get(v_self_1078_, 6);
lean_inc_ref(v_config_1080_);
v_dir_1081_ = lean_ctor_get(v_self_1078_, 4);
lean_inc_ref(v_dir_1081_);
lean_dec_ref(v_self_1078_);
v_buildDir_1082_ = lean_ctor_get(v_config_1080_, 5);
lean_inc_ref(v_buildDir_1082_);
lean_dec_ref(v_config_1080_);
v___x_1083_ = l_System_FilePath_normalize(v_buildDir_1082_);
v___x_1084_ = l_Lake_joinRelative(v_dir_1081_, v___x_1083_);
v___x_1085_ = l_Lake_removeDirAllIfExists(v___x_1084_);
lean_dec_ref(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lake_Package_clean(v_self_1086_);
return v_res_1088_;
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
