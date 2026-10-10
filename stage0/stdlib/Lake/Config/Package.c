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
lean_object* l_Lake_instInhabitedPackageConfig_default___redArg();
lean_object* l_Lake_OrdHashSet_empty___redArg();
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_Platform_target;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object* v_pkg_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object* v_pkg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(v_pkg_8_);
lean_dec(v_pkg_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(lean_object* v_k_10_, lean_object* v_v_11_, lean_object* v_t_12_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_size_13_; lean_object* v_k_14_; lean_object* v_v_15_; lean_object* v_l_16_; lean_object* v_r_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_297_; 
v_size_13_ = lean_ctor_get(v_t_12_, 0);
v_k_14_ = lean_ctor_get(v_t_12_, 1);
v_v_15_ = lean_ctor_get(v_t_12_, 2);
v_l_16_ = lean_ctor_get(v_t_12_, 3);
v_r_17_ = lean_ctor_get(v_t_12_, 4);
v_isSharedCheck_297_ = !lean_is_exclusive(v_t_12_);
if (v_isSharedCheck_297_ == 0)
{
v___x_19_ = v_t_12_;
v_isShared_20_ = v_isSharedCheck_297_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_r_17_);
lean_inc(v_l_16_);
lean_inc(v_v_15_);
lean_inc(v_k_14_);
lean_inc(v_size_13_);
lean_dec(v_t_12_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_297_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
uint8_t v___x_21_; 
v___x_21_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_10_, v_k_14_);
switch(v___x_21_)
{
case 0:
{
lean_object* v_impl_22_; lean_object* v___x_23_; 
lean_dec(v_size_13_);
v_impl_22_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_10_, v_v_11_, v_l_16_);
v___x_23_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_17_) == 0)
{
lean_object* v_size_24_; lean_object* v_size_25_; lean_object* v_k_26_; lean_object* v_v_27_; lean_object* v_l_28_; lean_object* v_r_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_size_24_ = lean_ctor_get(v_r_17_, 0);
v_size_25_ = lean_ctor_get(v_impl_22_, 0);
v_k_26_ = lean_ctor_get(v_impl_22_, 1);
v_v_27_ = lean_ctor_get(v_impl_22_, 2);
v_l_28_ = lean_ctor_get(v_impl_22_, 3);
v_r_29_ = lean_ctor_get(v_impl_22_, 4);
lean_inc(v_r_29_);
v___x_30_ = lean_unsigned_to_nat(3u);
v___x_31_ = lean_nat_mul(v___x_30_, v_size_24_);
v___x_32_ = lean_nat_dec_lt(v___x_31_, v_size_25_);
lean_dec(v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
lean_dec(v_r_29_);
v___x_33_ = lean_nat_add(v___x_23_, v_size_25_);
v___x_34_ = lean_nat_add(v___x_33_, v_size_24_);
lean_dec(v___x_33_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 3, v_impl_22_);
lean_ctor_set(v___x_19_, 0, v___x_34_);
v___x_36_ = v___x_19_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_impl_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_r_17_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
else
{
lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_103_; 
lean_inc(v_l_28_);
lean_inc(v_v_27_);
lean_inc(v_k_26_);
lean_inc(v_size_25_);
v_isSharedCheck_103_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; lean_object* v_unused_105_; lean_object* v_unused_106_; lean_object* v_unused_107_; lean_object* v_unused_108_; 
v_unused_104_ = lean_ctor_get(v_impl_22_, 4);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_impl_22_, 2);
lean_dec(v_unused_106_);
v_unused_107_ = lean_ctor_get(v_impl_22_, 1);
lean_dec(v_unused_107_);
v_unused_108_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_108_);
v___x_39_ = v_impl_22_;
v_isShared_40_ = v_isSharedCheck_103_;
goto v_resetjp_38_;
}
else
{
lean_dec(v_impl_22_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_103_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_size_41_; lean_object* v_size_42_; lean_object* v_k_43_; lean_object* v_v_44_; lean_object* v_l_45_; lean_object* v_r_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_size_41_ = lean_ctor_get(v_l_28_, 0);
v_size_42_ = lean_ctor_get(v_r_29_, 0);
v_k_43_ = lean_ctor_get(v_r_29_, 1);
v_v_44_ = lean_ctor_get(v_r_29_, 2);
v_l_45_ = lean_ctor_get(v_r_29_, 3);
v_r_46_ = lean_ctor_get(v_r_29_, 4);
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_nat_mul(v___x_47_, v_size_41_);
v___x_49_ = lean_nat_dec_lt(v_size_42_, v___x_48_);
lean_dec(v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_78_; 
lean_inc(v_r_46_);
lean_inc(v_l_45_);
lean_inc(v_v_44_);
lean_inc(v_k_43_);
v_isSharedCheck_78_ = !lean_is_exclusive(v_r_29_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; lean_object* v_unused_80_; lean_object* v_unused_81_; lean_object* v_unused_82_; lean_object* v_unused_83_; 
v_unused_79_ = lean_ctor_get(v_r_29_, 4);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v_r_29_, 3);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_r_29_, 2);
lean_dec(v_unused_81_);
v_unused_82_ = lean_ctor_get(v_r_29_, 1);
lean_dec(v_unused_82_);
v_unused_83_ = lean_ctor_get(v_r_29_, 0);
lean_dec(v_unused_83_);
v___x_51_ = v_r_29_;
v_isShared_52_ = v_isSharedCheck_78_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_r_29_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_78_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___x_66_; lean_object* v___y_68_; 
v___x_53_ = lean_nat_add(v___x_23_, v_size_25_);
lean_dec(v_size_25_);
v___x_54_ = lean_nat_add(v___x_53_, v_size_24_);
lean_dec(v___x_53_);
v___x_66_ = lean_nat_add(v___x_23_, v_size_41_);
if (lean_obj_tag(v_l_45_) == 0)
{
lean_object* v_size_76_; 
v_size_76_ = lean_ctor_get(v_l_45_, 0);
lean_inc(v_size_76_);
v___y_68_ = v_size_76_;
goto v___jp_67_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___y_68_ = v___x_77_;
goto v___jp_67_;
}
v___jp_55_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_nat_add(v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec(v___y_57_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 4, v_r_17_);
lean_ctor_set(v___x_51_, 3, v_r_46_);
lean_ctor_set(v___x_51_, 2, v_v_15_);
lean_ctor_set(v___x_51_, 1, v_k_14_);
lean_ctor_set(v___x_51_, 0, v___x_59_);
v___x_61_ = v___x_51_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_r_46_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v_r_17_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 4, v___x_61_);
lean_ctor_set(v___x_39_, 3, v___y_56_);
lean_ctor_set(v___x_39_, 2, v_v_44_);
lean_ctor_set(v___x_39_, 1, v_k_43_);
lean_ctor_set(v___x_39_, 0, v___x_54_);
v___x_63_ = v___x_39_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_k_43_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_v_44_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v___y_56_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_nat_add(v___x_66_, v___y_68_);
lean_dec(v___y_68_);
lean_dec(v___x_66_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_l_45_);
lean_ctor_set(v___x_19_, 3, v_l_28_);
lean_ctor_set(v___x_19_, 2, v_v_27_);
lean_ctor_set(v___x_19_, 1, v_k_26_);
lean_ctor_set(v___x_19_, 0, v___x_69_);
v___x_71_ = v___x_19_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v_l_45_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; 
v___x_72_ = lean_nat_add(v___x_23_, v_size_24_);
if (lean_obj_tag(v_r_46_) == 0)
{
lean_object* v_size_73_; 
v_size_73_ = lean_ctor_get(v_r_46_, 0);
lean_inc(v_size_73_);
v___y_56_ = v___x_71_;
v___y_57_ = v___x_72_;
v___y_58_ = v_size_73_;
goto v___jp_55_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___y_56_ = v___x_71_;
v___y_57_ = v___x_72_;
v___y_58_ = v___x_74_;
goto v___jp_55_;
}
}
}
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
lean_del_object(v___x_19_);
v___x_84_ = lean_nat_add(v___x_23_, v_size_25_);
lean_dec(v_size_25_);
v___x_85_ = lean_nat_add(v___x_84_, v_size_24_);
lean_dec(v___x_84_);
v___x_86_ = lean_nat_add(v___x_23_, v_size_24_);
v___x_87_ = lean_nat_add(v___x_86_, v_size_42_);
lean_dec(v___x_86_);
lean_inc_ref(v_r_17_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 4, v_r_17_);
lean_ctor_set(v___x_39_, 3, v_r_29_);
lean_ctor_set(v___x_39_, 2, v_v_15_);
lean_ctor_set(v___x_39_, 1, v_k_14_);
lean_ctor_set(v___x_39_, 0, v___x_87_);
v___x_89_ = v___x_39_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v_r_29_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v_r_17_);
v___x_89_ = v_reuseFailAlloc_102_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_isSharedCheck_96_ = !lean_is_exclusive(v_r_17_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; lean_object* v_unused_100_; lean_object* v_unused_101_; 
v_unused_97_ = lean_ctor_get(v_r_17_, 4);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_r_17_, 3);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_r_17_, 2);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v_r_17_, 1);
lean_dec(v_unused_100_);
v_unused_101_ = lean_ctor_get(v_r_17_, 0);
lean_dec(v_unused_101_);
v___x_91_ = v_r_17_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_dec(v_r_17_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___x_89_);
lean_ctor_set(v___x_91_, 3, v_l_28_);
lean_ctor_set(v___x_91_, 2, v_v_27_);
lean_ctor_set(v___x_91_, 1, v_k_26_);
lean_ctor_set(v___x_91_, 0, v___x_85_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v___x_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_109_; 
v_l_109_ = lean_ctor_get(v_impl_22_, 3);
if (lean_obj_tag(v_l_109_) == 0)
{
lean_object* v_r_110_; lean_object* v_k_111_; lean_object* v_v_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_123_; 
lean_inc_ref(v_l_109_);
v_r_110_ = lean_ctor_get(v_impl_22_, 4);
v_k_111_ = lean_ctor_get(v_impl_22_, 1);
v_v_112_ = lean_ctor_get(v_impl_22_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; 
v_unused_124_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_125_);
v___x_114_ = v_impl_22_;
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_r_110_);
lean_inc(v_v_112_);
lean_inc(v_k_111_);
lean_dec(v_impl_22_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 3, v_r_110_);
lean_ctor_set(v___x_114_, 2, v_v_15_);
lean_ctor_set(v___x_114_, 1, v_k_14_);
lean_ctor_set(v___x_114_, 0, v___x_23_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v_r_110_);
lean_ctor_set(v_reuseFailAlloc_122_, 4, v_r_110_);
v___x_118_ = v_reuseFailAlloc_122_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_120_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v___x_118_);
lean_ctor_set(v___x_19_, 3, v_l_109_);
lean_ctor_set(v___x_19_, 2, v_v_112_);
lean_ctor_set(v___x_19_, 1, v_k_111_);
lean_ctor_set(v___x_19_, 0, v___x_116_);
v___x_120_ = v___x_19_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_k_111_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_v_112_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_121_, 4, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_r_126_; 
v_r_126_ = lean_ctor_get(v_impl_22_, 4);
lean_inc(v_r_126_);
if (lean_obj_tag(v_r_126_) == 0)
{
lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_151_; 
lean_inc(v_l_109_);
v_k_127_ = lean_ctor_get(v_impl_22_, 1);
v_v_128_ = lean_ctor_get(v_impl_22_, 2);
v_isSharedCheck_151_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; 
v_unused_152_ = lean_ctor_get(v_impl_22_, 4);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_154_);
v___x_130_ = v_impl_22_;
v_isShared_131_ = v_isSharedCheck_151_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_v_128_);
lean_inc(v_k_127_);
lean_dec(v_impl_22_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_151_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_k_132_; lean_object* v_v_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_147_; 
v_k_132_ = lean_ctor_get(v_r_126_, 1);
v_v_133_ = lean_ctor_get(v_r_126_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_r_126_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; lean_object* v_unused_150_; 
v_unused_148_ = lean_ctor_get(v_r_126_, 4);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_r_126_, 3);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v_r_126_, 0);
lean_dec(v_unused_150_);
v___x_135_ = v_r_126_;
v_isShared_136_ = v_isSharedCheck_147_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_v_133_);
lean_inc(v_k_132_);
lean_dec(v_r_126_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_147_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(3u);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v_l_109_);
lean_ctor_set(v___x_135_, 3, v_l_109_);
lean_ctor_set(v___x_135_, 2, v_v_128_);
lean_ctor_set(v___x_135_, 1, v_k_127_);
lean_ctor_set(v___x_135_, 0, v___x_23_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_l_109_);
v___x_139_ = v_reuseFailAlloc_146_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v_l_109_);
lean_ctor_set(v___x_130_, 2, v_v_15_);
lean_ctor_set(v___x_130_, 1, v_k_14_);
lean_ctor_set(v___x_130_, 0, v___x_23_);
v___x_141_ = v___x_130_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_l_109_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v___x_141_);
lean_ctor_set(v___x_19_, 3, v___x_139_);
lean_ctor_set(v___x_19_, 2, v_v_133_);
lean_ctor_set(v___x_19_, 1, v_k_132_);
lean_ctor_set(v___x_19_, 0, v___x_137_);
v___x_143_ = v___x_19_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_132_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_133_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(2u);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_r_126_);
lean_ctor_set(v___x_19_, 3, v_impl_22_);
lean_ctor_set(v___x_19_, 0, v___x_155_);
v___x_157_ = v___x_19_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_impl_22_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_r_126_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
case 1:
{
lean_object* v___x_160_; 
lean_dec(v_v_15_);
lean_dec(v_k_14_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v_v_11_);
lean_ctor_set(v___x_19_, 1, v_k_10_);
v___x_160_ = v___x_19_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_13_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_10_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_v_11_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v_l_16_);
lean_ctor_set(v_reuseFailAlloc_161_, 4, v_r_17_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
default: 
{
lean_object* v_impl_162_; lean_object* v___x_163_; 
lean_dec(v_size_13_);
v_impl_162_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_10_, v_v_11_, v_r_17_);
v___x_163_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_16_) == 0)
{
lean_object* v_size_164_; lean_object* v_size_165_; lean_object* v_k_166_; lean_object* v_v_167_; lean_object* v_l_168_; lean_object* v_r_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_size_164_ = lean_ctor_get(v_l_16_, 0);
v_size_165_ = lean_ctor_get(v_impl_162_, 0);
v_k_166_ = lean_ctor_get(v_impl_162_, 1);
v_v_167_ = lean_ctor_get(v_impl_162_, 2);
v_l_168_ = lean_ctor_get(v_impl_162_, 3);
lean_inc(v_l_168_);
v_r_169_ = lean_ctor_get(v_impl_162_, 4);
v___x_170_ = lean_unsigned_to_nat(3u);
v___x_171_ = lean_nat_mul(v___x_170_, v_size_164_);
v___x_172_ = lean_nat_dec_lt(v___x_171_, v_size_165_);
lean_dec(v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
lean_dec(v_l_168_);
v___x_173_ = lean_nat_add(v___x_163_, v_size_164_);
v___x_174_ = lean_nat_add(v___x_173_, v_size_165_);
lean_dec(v___x_173_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_impl_162_);
lean_ctor_set(v___x_19_, 0, v___x_174_);
v___x_176_ = v___x_19_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_l_16_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v_impl_162_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
else
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_241_; 
lean_inc(v_r_169_);
lean_inc(v_v_167_);
lean_inc(v_k_166_);
lean_inc(v_size_165_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_impl_162_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_242_ = lean_ctor_get(v_impl_162_, 4);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_impl_162_, 3);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_impl_162_, 2);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_impl_162_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_impl_162_, 0);
lean_dec(v_unused_246_);
v___x_179_ = v_impl_162_;
v_isShared_180_ = v_isSharedCheck_241_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_impl_162_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_241_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_size_181_; lean_object* v_k_182_; lean_object* v_v_183_; lean_object* v_l_184_; lean_object* v_r_185_; lean_object* v_size_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_size_181_ = lean_ctor_get(v_l_168_, 0);
v_k_182_ = lean_ctor_get(v_l_168_, 1);
v_v_183_ = lean_ctor_get(v_l_168_, 2);
v_l_184_ = lean_ctor_get(v_l_168_, 3);
v_r_185_ = lean_ctor_get(v_l_168_, 4);
v_size_186_ = lean_ctor_get(v_r_169_, 0);
v___x_187_ = lean_unsigned_to_nat(2u);
v___x_188_ = lean_nat_mul(v___x_187_, v_size_186_);
v___x_189_ = lean_nat_dec_lt(v_size_181_, v___x_188_);
lean_dec(v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_217_; 
lean_inc(v_r_185_);
lean_inc(v_l_184_);
lean_inc(v_v_183_);
lean_inc(v_k_182_);
v_isSharedCheck_217_ = !lean_is_exclusive(v_l_168_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; lean_object* v_unused_221_; lean_object* v_unused_222_; 
v_unused_218_ = lean_ctor_get(v_l_168_, 4);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_l_168_, 3);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_l_168_, 2);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_l_168_, 1);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_l_168_, 0);
lean_dec(v_unused_222_);
v___x_191_ = v_l_168_;
v_isShared_192_ = v_isSharedCheck_217_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_l_168_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_217_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_207_; 
v___x_193_ = lean_nat_add(v___x_163_, v_size_164_);
v___x_194_ = lean_nat_add(v___x_193_, v_size_165_);
lean_dec(v_size_165_);
if (lean_obj_tag(v_l_184_) == 0)
{
lean_object* v_size_215_; 
v_size_215_ = lean_ctor_get(v_l_184_, 0);
lean_inc(v_size_215_);
v___y_207_ = v_size_215_;
goto v___jp_206_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___y_207_ = v___x_216_;
goto v___jp_206_;
}
v___jp_195_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_nat_add(v___y_196_, v___y_198_);
lean_dec(v___y_198_);
lean_dec(v___y_196_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v_r_169_);
lean_ctor_set(v___x_191_, 3, v_r_185_);
lean_ctor_set(v___x_191_, 2, v_v_167_);
lean_ctor_set(v___x_191_, 1, v_k_166_);
lean_ctor_set(v___x_191_, 0, v___x_199_);
v___x_201_ = v___x_191_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_166_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_167_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_r_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_r_169_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 4, v___x_201_);
lean_ctor_set(v___x_179_, 3, v___y_197_);
lean_ctor_set(v___x_179_, 2, v_v_183_);
lean_ctor_set(v___x_179_, 1, v_k_182_);
lean_ctor_set(v___x_179_, 0, v___x_194_);
v___x_203_ = v___x_179_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_182_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_183_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___y_197_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_nat_add(v___x_193_, v___y_207_);
lean_dec(v___y_207_);
lean_dec(v___x_193_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_l_184_);
lean_ctor_set(v___x_19_, 0, v___x_208_);
v___x_210_ = v___x_19_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_16_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_l_184_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_nat_add(v___x_163_, v_size_186_);
if (lean_obj_tag(v_r_185_) == 0)
{
lean_object* v_size_212_; 
v_size_212_ = lean_ctor_get(v_r_185_, 0);
lean_inc(v_size_212_);
v___y_196_ = v___x_211_;
v___y_197_ = v___x_210_;
v___y_198_ = v_size_212_;
goto v___jp_195_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___y_196_ = v___x_211_;
v___y_197_ = v___x_210_;
v___y_198_ = v___x_213_;
goto v___jp_195_;
}
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
lean_del_object(v___x_19_);
v___x_223_ = lean_nat_add(v___x_163_, v_size_164_);
v___x_224_ = lean_nat_add(v___x_223_, v_size_165_);
lean_dec(v_size_165_);
v___x_225_ = lean_nat_add(v___x_223_, v_size_181_);
lean_dec(v___x_223_);
lean_inc_ref(v_l_16_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 4, v_l_168_);
lean_ctor_set(v___x_179_, 3, v_l_16_);
lean_ctor_set(v___x_179_, 2, v_v_15_);
lean_ctor_set(v___x_179_, 1, v_k_14_);
lean_ctor_set(v___x_179_, 0, v___x_225_);
v___x_227_ = v___x_179_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_l_16_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_l_168_);
v___x_227_ = v_reuseFailAlloc_240_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_isSharedCheck_234_ = !lean_is_exclusive(v_l_16_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_235_ = lean_ctor_get(v_l_16_, 4);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_l_16_, 3);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_l_16_, 2);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_l_16_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_l_16_, 0);
lean_dec(v_unused_239_);
v___x_229_ = v_l_16_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_l_16_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v_r_169_);
lean_ctor_set(v___x_229_, 3, v___x_227_);
lean_ctor_set(v___x_229_, 2, v_v_167_);
lean_ctor_set(v___x_229_, 1, v_k_166_);
lean_ctor_set(v___x_229_, 0, v___x_224_);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_166_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_v_167_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_r_169_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_247_; 
v_l_247_ = lean_ctor_get(v_impl_162_, 3);
lean_inc(v_l_247_);
if (lean_obj_tag(v_l_247_) == 0)
{
lean_object* v_r_248_; lean_object* v_k_249_; lean_object* v_v_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
v_r_248_ = lean_ctor_get(v_impl_162_, 4);
v_k_249_ = lean_ctor_get(v_impl_162_, 1);
v_v_250_ = lean_ctor_get(v_impl_162_, 2);
v_isSharedCheck_273_ = !lean_is_exclusive(v_impl_162_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_274_ = lean_ctor_get(v_impl_162_, 3);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_impl_162_, 0);
lean_dec(v_unused_275_);
v___x_252_ = v_impl_162_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_r_248_);
lean_inc(v_v_250_);
lean_inc(v_k_249_);
lean_dec(v_impl_162_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_269_; 
v_k_254_ = lean_ctor_get(v_l_247_, 1);
v_v_255_ = lean_ctor_get(v_l_247_, 2);
v_isSharedCheck_269_ = !lean_is_exclusive(v_l_247_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_270_ = lean_ctor_get(v_l_247_, 4);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_l_247_, 3);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_l_247_, 0);
lean_dec(v_unused_272_);
v___x_257_ = v_l_247_;
v_isShared_258_ = v_isSharedCheck_269_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_v_255_);
lean_inc(v_k_254_);
lean_dec(v_l_247_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_269_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_248_, 2);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 4, v_r_248_);
lean_ctor_set(v___x_257_, 3, v_r_248_);
lean_ctor_set(v___x_257_, 2, v_v_15_);
lean_ctor_set(v___x_257_, 1, v_k_14_);
lean_ctor_set(v___x_257_, 0, v___x_163_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_r_248_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_r_248_);
v___x_261_ = v_reuseFailAlloc_268_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
lean_inc(v_r_248_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 3, v_r_248_);
lean_ctor_set(v___x_252_, 0, v___x_163_);
v___x_263_ = v___x_252_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_r_248_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_r_248_);
v___x_263_ = v_reuseFailAlloc_267_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_265_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v___x_263_);
lean_ctor_set(v___x_19_, 3, v___x_261_);
lean_ctor_set(v___x_19_, 2, v_v_255_);
lean_ctor_set(v___x_19_, 1, v_k_254_);
lean_ctor_set(v___x_19_, 0, v___x_259_);
v___x_265_ = v___x_19_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_k_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_v_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
else
{
lean_object* v_r_276_; 
v_r_276_ = lean_ctor_get(v_impl_162_, 4);
lean_inc(v_r_276_);
if (lean_obj_tag(v_r_276_) == 0)
{
lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_289_; 
v_k_277_ = lean_ctor_get(v_impl_162_, 1);
v_v_278_ = lean_ctor_get(v_impl_162_, 2);
v_isSharedCheck_289_ = !lean_is_exclusive(v_impl_162_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_290_ = lean_ctor_get(v_impl_162_, 4);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_impl_162_, 3);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_impl_162_, 0);
lean_dec(v_unused_292_);
v___x_280_ = v_impl_162_;
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_v_278_);
lean_inc(v_k_277_);
lean_dec(v_impl_162_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(3u);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 4, v_l_247_);
lean_ctor_set(v___x_280_, 2, v_v_15_);
lean_ctor_set(v___x_280_, 1, v_k_14_);
lean_ctor_set(v___x_280_, 0, v___x_163_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_l_247_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_l_247_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_r_276_);
lean_ctor_set(v___x_19_, 3, v___x_284_);
lean_ctor_set(v___x_19_, 2, v_v_278_);
lean_ctor_set(v___x_19_, 1, v_k_277_);
lean_ctor_set(v___x_19_, 0, v___x_282_);
v___x_286_ = v___x_19_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_r_276_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(2u);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 4, v_impl_162_);
lean_ctor_set(v___x_19_, 3, v_r_276_);
lean_ctor_set(v___x_19_, 0, v___x_293_);
v___x_295_ = v___x_19_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_14_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_15_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_r_276_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_impl_162_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
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
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_k_10_);
lean_ctor_set(v___x_299_, 2, v_v_11_);
lean_ctor_set(v___x_299_, 3, v_t_12_);
lean_ctor_set(v___x_299_, 4, v_t_12_);
return v___x_299_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(lean_object* v_as_300_, size_t v_i_301_, size_t v_stop_302_, lean_object* v_b_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_usize_dec_eq(v_i_301_, v_stop_302_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v_name_306_; lean_object* v___x_307_; size_t v___x_308_; size_t v___x_309_; 
v___x_305_ = lean_array_uget_borrowed(v_as_300_, v_i_301_);
v_name_306_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v___x_305_);
lean_inc(v_name_306_);
v___x_307_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_name_306_, v___x_305_, v_b_303_);
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_add(v_i_301_, v___x_308_);
v_i_301_ = v___x_309_;
v_b_303_ = v___x_307_;
goto _start;
}
else
{
return v_b_303_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_300_ = stack[0].m_obj;
size_t v_i_301_ = stack[1].m_num;
size_t v_stop_302_ = stack[2].m_num;
lean_object* v_b_303_ = stack[3].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v_as_300_, v_i_301_, v_stop_302_, v_b_303_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1___boxed(lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_stop_314_, lean_object* v_b_315_){
_start:
{
size_t v_i_boxed_316_; size_t v_stop_boxed_317_; lean_object* v_res_318_; 
v_i_boxed_316_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_stop_boxed_317_ = lean_unbox_usize(v_stop_314_);
lean_dec(v_stop_314_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v_as_312_, v_i_boxed_316_, v_stop_boxed_317_, v_b_315_);
lean_dec_ref(v_as_312_);
return v_res_318_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__2(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v___x_323_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__4(void){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = 0;
v___x_327_ = lean_box(0);
v___x_328_ = l_Lean_Name_toString(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__6(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__5));
v___x_331_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__4, &l_Lake_instInhabitedPackage_default___closed__4_once, _init_l_Lake_instInhabitedPackage_default___closed__4);
v___x_332_ = lean_string_append(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__7(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l_System_Platform_target;
v___x_334_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__6, &l_Lake_instInhabitedPackage_default___closed__6_once, _init_l_Lake_instInhabitedPackage_default___closed__6);
v___x_335_ = lean_string_append(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__9(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__8));
v___x_338_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__7, &l_Lake_instInhabitedPackage_default___closed__7_once, _init_l_Lake_instInhabitedPackage_default___closed__7);
v___x_339_ = lean_string_append(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__10(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_341_ = lean_array_get_size(v___x_340_);
return v___x_341_;
}
}
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__11(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__12(void){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_346_ = lean_nat_dec_le(v___x_345_, v___x_345_);
return v___x_346_;
}
}
static size_t _init_l_Lake_instInhabitedPackage_default___closed__13(void){
_start:
{
lean_object* v___x_347_; size_t v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_348_ = lean_usize_of_nat(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__14(void){
_start:
{
lean_object* v___x_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = lean_box(1);
v___x_350_ = lean_usize_once(&l_Lake_instInhabitedPackage_default___closed__13, &l_Lake_instInhabitedPackage_default___closed__13_once, _init_l_Lake_instInhabitedPackage_default___closed__13);
v___x_351_ = ((size_t)0ULL);
v___x_352_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v___x_352_, v___x_351_, v___x_350_, v___x_349_);
return v___x_353_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_371_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_box(0);
v___x_356_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_357_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_358_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__2, &l_Lake_instInhabitedPackage_default___closed__2_once, _init_l_Lake_instInhabitedPackage_default___closed__2);
v___x_359_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_376_ = lean_box(1);
v___x_377_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__11, &l_Lake_instInhabitedPackage_default___closed__11_once, _init_l_Lake_instInhabitedPackage_default___closed__11);
if (v___x_377_ == 0)
{
v___y_371_ = v___x_376_;
goto v___jp_370_;
}
else
{
uint8_t v___x_378_; 
v___x_378_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__12, &l_Lake_instInhabitedPackage_default___closed__12_once, _init_l_Lake_instInhabitedPackage_default___closed__12);
if (v___x_378_ == 0)
{
if (v___x_377_ == 0)
{
v___y_371_ = v___x_376_;
goto v___jp_370_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_371_ = v___x_379_;
goto v___jp_370_;
}
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_371_ = v___x_380_;
goto v___jp_370_;
}
}
v___jp_360_:
{
lean_object* v_testDriver_367_; lean_object* v_lintDriver_368_; lean_object* v___x_369_; 
v_testDriver_367_ = lean_ctor_get(v___x_358_, 12);
v_lintDriver_368_ = lean_ctor_get(v___x_358_, 14);
lean_inc_ref(v_lintDriver_368_);
lean_inc_ref(v_testDriver_367_);
lean_inc_ref(v___y_366_);
lean_inc_ref(v___y_364_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
v___x_369_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v___x_369_, 0, v___x_354_);
lean_ctor_set(v___x_369_, 1, v___x_355_);
lean_ctor_set(v___x_369_, 2, v___x_356_);
lean_ctor_set(v___x_369_, 3, v___x_355_);
lean_ctor_set(v___x_369_, 4, v___x_357_);
lean_ctor_set(v___x_369_, 5, v___x_357_);
lean_ctor_set(v___x_369_, 6, v___x_358_);
lean_ctor_set(v___x_369_, 7, v___x_357_);
lean_ctor_set(v___x_369_, 8, v___x_357_);
lean_ctor_set(v___x_369_, 9, v___x_357_);
lean_ctor_set(v___x_369_, 10, v___x_357_);
lean_ctor_set(v___x_369_, 11, v___x_357_);
lean_ctor_set(v___x_369_, 12, v___x_359_);
lean_ctor_set(v___x_369_, 13, v___x_359_);
lean_ctor_set(v___x_369_, 14, v___x_359_);
lean_ctor_set(v___x_369_, 15, v___x_359_);
lean_ctor_set(v___x_369_, 16, v___y_362_);
lean_ctor_set(v___x_369_, 17, v___y_363_);
lean_ctor_set(v___x_369_, 18, v___y_361_);
lean_ctor_set(v___x_369_, 19, v___y_365_);
lean_ctor_set(v___x_369_, 20, v___y_364_);
lean_ctor_set(v___x_369_, 21, v___y_366_);
lean_ctor_set(v___x_369_, 22, v_testDriver_367_);
lean_ctor_set(v___x_369_, 23, v_lintDriver_368_);
return v___x_369_;
}
v___jp_370_:
{
lean_object* v_buildArchive_372_; lean_object* v___x_373_; 
v_buildArchive_372_ = lean_ctor_get(v___x_358_, 11);
v___x_373_ = lean_box(1);
if (lean_obj_tag(v_buildArchive_372_) == 1)
{
lean_object* v_val_374_; 
v_val_374_ = lean_ctor_get(v_buildArchive_372_, 0);
v___y_361_ = v___x_373_;
v___y_362_ = v___y_371_;
v___y_363_ = v___x_359_;
v___y_364_ = v___x_359_;
v___y_365_ = v___x_359_;
v___y_366_ = v_val_374_;
goto v___jp_360_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__9, &l_Lake_instInhabitedPackage_default___closed__9_once, _init_l_Lake_instInhabitedPackage_default___closed__9);
v___y_361_ = v___x_373_;
v___y_362_ = v___y_371_;
v___y_363_ = v___x_359_;
v___y_364_ = v___x_359_;
v___y_365_ = v___x_359_;
v___y_366_ = v___x_375_;
goto v___jp_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object* v_00_u03b2_381_, lean_object* v_k_382_, lean_object* v_v_383_, lean_object* v_t_384_, lean_object* v_hl_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_382_, v_v_383_, v_t_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lake_instInhabitedPackage_default;
return v___x_387_;
}
}
uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_388_){
_start:
{
lean_object* v_keyName_389_; 
v_keyName_389_ = lean_ctor_get(v_pkg_388_, 2);
if (lean_obj_tag(v_keyName_389_) == 0)
{
uint64_t v___x_390_; 
v___x_390_ = 1723ULL;
return v___x_390_;
}
else
{
uint64_t v_hash_391_; 
v_hash_391_ = lean_ctor_get_uint64(v_keyName_389_, sizeof(void*)*2);
return v_hash_391_;
}
}
}
LEAN_EXPORT void l_Lake_Package_instHashable___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_388_ = stack[0].m_obj;
uint64_t v_res_392_;
v_res_392_ = l_Lake_Package_instHashable___lam__0(v_pkg_388_);
stack->m_num = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_393_){
_start:
{
uint64_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lake_Package_instHashable___lam__0(v_pkg_393_);
lean_dec_ref(v_pkg_393_);
v_r_395_ = lean_box_uint64(v_res_394_);
return v_r_395_;
}
}
uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_398_, lean_object* v_p2_399_){
_start:
{
lean_object* v_wsIdx_400_; lean_object* v_wsIdx_401_; uint8_t v___x_402_; 
v_wsIdx_400_ = lean_ctor_get(v_p1_398_, 0);
v_wsIdx_401_ = lean_ctor_get(v_p2_399_, 0);
v___x_402_ = lean_nat_dec_eq(v_wsIdx_400_, v_wsIdx_401_);
return v___x_402_;
}
}
LEAN_EXPORT void l_Lake_Package_instBEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p1_398_ = stack[0].m_obj;
lean_object* v_p2_399_ = stack[1].m_obj;
uint8_t v_res_403_;
v_res_403_ = l_Lake_Package_instBEq___lam__0(v_p1_398_, v_p2_399_);
stack->m_num = v_res_403_;
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_404_, lean_object* v_p2_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Lake_Package_instBEq___lam__0(v_p1_404_, v_p2_405_);
lean_dec_ref(v_p2_405_);
lean_dec_ref(v_p1_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_410_){
_start:
{
lean_object* v_baseName_411_; uint8_t v___x_412_; lean_object* v___x_413_; 
v_baseName_411_ = lean_ctor_get(v_self_410_, 1);
lean_inc(v_baseName_411_);
lean_dec_ref(v_self_410_);
v___x_412_ = 0;
v___x_413_ = l_Lean_Name_toString(v_baseName_411_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_414_){
_start:
{
lean_object* v_keyName_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_keyName_415_ = lean_ctor_get(v_x_414_, 2);
lean_inc(v_keyName_415_);
lean_dec_ref(v_x_414_);
v___x_416_ = 1;
v___x_417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_415_, v___x_416_);
v___x_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_421_){
_start:
{
lean_object* v_baseName_422_; uint8_t v___x_423_; lean_object* v___x_424_; 
v_baseName_422_ = lean_ctor_get(v_x_421_, 1);
lean_inc(v_baseName_422_);
lean_dec_ref(v_x_421_);
v___x_423_ = 0;
v___x_424_ = l_Lean_Name_toString(v_baseName_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_427_){
_start:
{
lean_object* v_baseName_428_; 
v_baseName_428_ = lean_ctor_get(v_self_427_, 1);
lean_inc(v_baseName_428_);
return v_baseName_428_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lake_Package_name(v_self_429_);
lean_dec_ref(v_self_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_431_){
_start:
{
lean_object* v_origName_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v_origName_432_ = lean_ctor_get(v_self_431_, 3);
lean_inc(v_origName_432_);
lean_dec_ref(v_self_431_);
v___x_433_ = 0;
v___x_434_ = l_Lean_Name_toString(v_origName_432_, v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_unsigned_to_nat(16u);
v___x_437_ = lean_mk_array(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_441_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_442_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(lean_object* v_self_444_){
_start:
{
lean_inc_ref(v_self_444_);
return v_self_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed(lean_object* v_self_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(v_self_445_);
lean_dec_ref(v_self_445_);
return v_res_446_;
}
}
lean_object* l_Lake_NPackage_instCoeOutPackage___redArg(){
_start:
{
lean_object* v___f_449_; 
v___f_449_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_449_;
}
}
LEAN_EXPORT void l_Lake_NPackage_instCoeOutPackage___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_450_;
v_res_450_ = l_Lake_NPackage_instCoeOutPackage___redArg();
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___boxed(lean_object* v___dummy_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_NPackage_instCoeOutPackage___redArg();
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_NPackage_instCoeOutPackage(v_n_455_);
lean_dec(v_n_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_457_){
_start:
{
lean_inc_ref(v_pkg_457_);
return v_pkg_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_458_);
lean_dec_ref(v_pkg_458_);
return v_res_459_;
}
}
lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___y_462_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_460_ = stack[0].m_obj;
lean_object* v___y_461_ = stack[1].m_obj;
lean_object* v___y_462_ = stack[2].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(v_x_460_, v___y_461_, v___y_462_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed(lean_object* v_x_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(v_x_467_, v___y_468_, v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v_x_467_);
return v_res_471_;
}
}
lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg(){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_474_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPostUpdateHook_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_475_;
v_res_475_ = l_Lake_instInhabitedPostUpdateHook_default___redArg();
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___boxed(lean_object* v___dummy_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lake_instInhabitedPostUpdateHook_default___redArg();
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_478_){
_start:
{
lean_object* v___f_479_; 
v___f_479_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_480_);
lean_dec(v_pkgName_480_);
return v_res_481_;
}
}
lean_object* l_Lake_instInhabitedPostUpdateHook___redArg(){
_start:
{
lean_object* v___f_483_; 
v___f_483_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_483_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPostUpdateHook___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_484_;
v_res_484_ = l_Lake_instInhabitedPostUpdateHook___redArg();
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg___boxed(lean_object* v___dummy_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lake_instInhabitedPostUpdateHook___redArg();
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_487_){
_start:
{
lean_object* v___f_488_; 
v___f_488_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lake_instInhabitedPostUpdateHook(v_a_489_);
lean_dec(v_a_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_491_){
_start:
{
lean_inc_ref(v_a_491_);
return v_a_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_492_);
lean_dec_ref(v_a_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_494_, lean_object* v_a_495_){
_start:
{
lean_inc_ref(v_a_495_);
return v_a_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_496_, v_a_497_);
lean_dec_ref(v_a_497_);
lean_dec(v_name_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_500_, 0, v_name_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_501_){
_start:
{
lean_inc(v_a_501_);
return v_a_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_502_);
lean_dec(v_a_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_504_, lean_object* v_a_505_){
_start:
{
lean_inc(v_a_505_);
return v_a_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec(v_name_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_510_, 0, v_name_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_511_){
_start:
{
lean_inc_ref(v_inst_511_);
return v_inst_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_512_);
lean_dec_ref(v_inst_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_514_, lean_object* v_inst_515_){
_start:
{
lean_inc_ref(v_inst_515_);
return v_inst_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_516_, v_inst_517_);
lean_dec_ref(v_inst_517_);
lean_dec(v_name_516_);
return v_res_518_;
}
}
uint8_t l_Lake_Package_isRoot(lean_object* v_self_526_){
_start:
{
lean_object* v_wsIdx_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_wsIdx_527_ = lean_ctor_get(v_self_526_, 0);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_nat_dec_eq(v_wsIdx_527_, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lake_Package_isRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_526_ = stack[0].m_obj;
uint8_t v_res_530_;
v_res_530_ = l_Lake_Package_isRoot(v_self_526_);
stack->m_num = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Lake_Package_isRoot(v_self_531_);
lean_dec_ref(v_self_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
uint8_t l_Lake_Package_bootstrap(lean_object* v_self_534_){
_start:
{
lean_object* v_config_535_; uint8_t v_bootstrap_536_; 
v_config_535_ = lean_ctor_get(v_self_534_, 6);
v_bootstrap_536_ = lean_ctor_get_uint8(v_config_535_, sizeof(void*)*28);
return v_bootstrap_536_;
}
}
LEAN_EXPORT void l_Lake_Package_bootstrap_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_534_ = stack[0].m_obj;
uint8_t v_res_537_;
v_res_537_ = l_Lake_Package_bootstrap(v_self_534_);
stack->m_num = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Lake_Package_bootstrap(v_self_538_);
lean_dec_ref(v_self_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_541_){
_start:
{
lean_object* v_config_542_; uint8_t v_bootstrap_543_; 
v_config_542_ = lean_ctor_get(v_self_541_, 6);
v_bootstrap_543_ = lean_ctor_get_uint8(v_config_542_, sizeof(void*)*28);
if (v_bootstrap_543_ == 0)
{
lean_object* v_origName_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_origName_544_ = lean_ctor_get(v_self_541_, 3);
lean_inc(v_origName_544_);
lean_dec_ref(v_self_541_);
v___x_545_ = l_Lean_Name_toString(v_origName_544_, v_bootstrap_543_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v_self_541_);
v___x_547_ = lean_box(0);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_548_){
_start:
{
lean_object* v_config_549_; lean_object* v_version_550_; 
v_config_549_ = lean_ctor_get(v_self_548_, 6);
v_version_550_ = lean_ctor_get(v_config_549_, 16);
lean_inc_ref(v_version_550_);
return v_version_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lake_Package_version(v_self_551_);
lean_dec_ref(v_self_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_553_){
_start:
{
lean_object* v_config_554_; lean_object* v_versionTags_555_; 
v_config_554_ = lean_ctor_get(v_self_553_, 6);
v_versionTags_555_ = lean_ctor_get(v_config_554_, 17);
lean_inc_ref(v_versionTags_555_);
return v_versionTags_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_Package_versionTags(v_self_556_);
lean_dec_ref(v_self_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_558_){
_start:
{
lean_object* v_config_559_; lean_object* v_description_560_; 
v_config_559_ = lean_ctor_get(v_self_558_, 6);
v_description_560_ = lean_ctor_get(v_config_559_, 18);
lean_inc_ref(v_description_560_);
return v_description_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_Package_description(v_self_561_);
lean_dec_ref(v_self_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_563_){
_start:
{
lean_object* v_config_564_; lean_object* v_keywords_565_; 
v_config_564_ = lean_ctor_get(v_self_563_, 6);
v_keywords_565_ = lean_ctor_get(v_config_564_, 19);
lean_inc_ref(v_keywords_565_);
return v_keywords_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lake_Package_keywords(v_self_566_);
lean_dec_ref(v_self_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_568_){
_start:
{
lean_object* v_config_569_; lean_object* v_homepage_570_; 
v_config_569_ = lean_ctor_get(v_self_568_, 6);
v_homepage_570_ = lean_ctor_get(v_config_569_, 20);
lean_inc_ref(v_homepage_570_);
return v_homepage_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lake_Package_homepage(v_self_571_);
lean_dec_ref(v_self_571_);
return v_res_572_;
}
}
uint8_t l_Lake_Package_reservoir(lean_object* v_self_573_){
_start:
{
lean_object* v_config_574_; uint8_t v_reservoir_575_; 
v_config_574_ = lean_ctor_get(v_self_573_, 6);
v_reservoir_575_ = lean_ctor_get_uint8(v_config_574_, sizeof(void*)*28 + 3);
return v_reservoir_575_;
}
}
LEAN_EXPORT void l_Lake_Package_reservoir_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_573_ = stack[0].m_obj;
uint8_t v_res_576_;
v_res_576_ = l_Lake_Package_reservoir(v_self_573_);
stack->m_num = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_Lake_Package_reservoir(v_self_577_);
lean_dec_ref(v_self_577_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_580_){
_start:
{
lean_object* v_config_581_; lean_object* v_license_582_; 
v_config_581_ = lean_ctor_get(v_self_580_, 6);
v_license_582_ = lean_ctor_get(v_config_581_, 21);
lean_inc_ref(v_license_582_);
return v_license_582_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lake_Package_license(v_self_583_);
lean_dec_ref(v_self_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_605_){
_start:
{
lean_object* v_config_606_; lean_object* v_licenseFiles_607_; lean_object* v___f_608_; lean_object* v___x_609_; size_t v_sz_610_; size_t v___x_611_; lean_object* v___x_612_; 
v_config_606_ = lean_ctor_get(v_self_605_, 6);
lean_inc_ref(v_config_606_);
lean_dec_ref(v_self_605_);
v_licenseFiles_607_ = lean_ctor_get(v_config_606_, 22);
lean_inc_ref(v_licenseFiles_607_);
lean_dec_ref(v_config_606_);
v___f_608_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_609_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_610_ = lean_array_size(v_licenseFiles_607_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_609_, v___f_608_, v_sz_610_, v___x_611_, v_licenseFiles_607_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = l_System_FilePath_normalize(v_x_614_);
v___x_616_ = l_Lake_joinRelative(v_dir_613_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_617_){
_start:
{
lean_object* v_config_618_; lean_object* v_dir_619_; lean_object* v_licenseFiles_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; size_t v_sz_624_; size_t v___x_625_; lean_object* v___x_626_; size_t v_sz_627_; lean_object* v___x_628_; 
v_config_618_ = lean_ctor_get(v_self_617_, 6);
lean_inc_ref(v_config_618_);
v_dir_619_ = lean_ctor_get(v_self_617_, 4);
lean_inc_ref(v_dir_619_);
lean_dec_ref(v_self_617_);
v_licenseFiles_620_ = lean_ctor_get(v_config_618_, 22);
lean_inc_ref(v_licenseFiles_620_);
lean_dec_ref(v_config_618_);
v___f_621_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_622_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_622_, 0, v_dir_619_);
v___x_623_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_624_ = lean_array_size(v_licenseFiles_620_);
v___x_625_ = ((size_t)0ULL);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_623_, v___f_621_, v_sz_624_, v___x_625_, v_licenseFiles_620_);
v_sz_627_ = lean_array_size(v___x_626_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_623_, v___f_622_, v_sz_627_, v___x_625_, v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_629_){
_start:
{
lean_object* v_config_630_; lean_object* v_readmeFile_631_; lean_object* v___x_632_; 
v_config_630_ = lean_ctor_get(v_self_629_, 6);
lean_inc_ref(v_config_630_);
lean_dec_ref(v_self_629_);
v_readmeFile_631_ = lean_ctor_get(v_config_630_, 23);
lean_inc_ref(v_readmeFile_631_);
lean_dec_ref(v_config_630_);
v___x_632_ = l_System_FilePath_normalize(v_readmeFile_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_633_){
_start:
{
lean_object* v_config_634_; lean_object* v_dir_635_; lean_object* v_readmeFile_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_config_634_ = lean_ctor_get(v_self_633_, 6);
lean_inc_ref(v_config_634_);
v_dir_635_ = lean_ctor_get(v_self_633_, 4);
lean_inc_ref(v_dir_635_);
lean_dec_ref(v_self_633_);
v_readmeFile_636_ = lean_ctor_get(v_config_634_, 23);
lean_inc_ref(v_readmeFile_636_);
lean_dec_ref(v_config_634_);
v___x_637_ = l_System_FilePath_normalize(v_readmeFile_636_);
v___x_638_ = l_Lake_joinRelative(v_dir_635_, v___x_637_);
return v___x_638_;
}
}
lean_object* l_Lake_Package_relLakeDir___redArg(){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lake_defaultLakeDir;
return v___x_640_;
}
}
LEAN_EXPORT void l_Lake_Package_relLakeDir___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_641_;
v_res_641_ = l_Lake_Package_relLakeDir___redArg();
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg___boxed(lean_object* v___dummy_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lake_Package_relLakeDir___redArg();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lake_defaultLakeDir;
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lake_Package_relLakeDir(v_x_646_);
lean_dec_ref(v_x_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_648_){
_start:
{
lean_object* v_dir_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_dir_649_ = lean_ctor_get(v_self_648_, 4);
lean_inc_ref(v_dir_649_);
lean_dec_ref(v_self_648_);
v___x_650_ = l_Lake_defaultLakeDir;
v___x_651_ = l_Lake_joinRelative(v_dir_649_, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_652_){
_start:
{
lean_object* v_config_653_; lean_object* v_toWorkspaceConfig_654_; lean_object* v___x_655_; 
v_config_653_ = lean_ctor_get(v_self_652_, 6);
lean_inc_ref(v_config_653_);
lean_dec_ref(v_self_652_);
v_toWorkspaceConfig_654_ = lean_ctor_get(v_config_653_, 0);
lean_inc_ref(v_toWorkspaceConfig_654_);
lean_dec_ref(v_config_653_);
v___x_655_ = l_System_FilePath_normalize(v_toWorkspaceConfig_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_656_){
_start:
{
lean_object* v_config_657_; lean_object* v_dir_658_; lean_object* v_toWorkspaceConfig_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_config_657_ = lean_ctor_get(v_self_656_, 6);
lean_inc_ref(v_config_657_);
v_dir_658_ = lean_ctor_get(v_self_656_, 4);
lean_inc_ref(v_dir_658_);
lean_dec_ref(v_self_656_);
v_toWorkspaceConfig_659_ = lean_ctor_get(v_config_657_, 0);
lean_inc_ref(v_toWorkspaceConfig_659_);
lean_dec_ref(v_config_657_);
v___x_660_ = l_System_FilePath_normalize(v_toWorkspaceConfig_659_);
v___x_661_ = l_Lake_joinRelative(v_dir_658_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_662_){
_start:
{
lean_object* v_dir_663_; lean_object* v_relManifestFile_664_; lean_object* v___x_665_; 
v_dir_663_ = lean_ctor_get(v_self_662_, 4);
lean_inc_ref(v_dir_663_);
v_relManifestFile_664_ = lean_ctor_get(v_self_662_, 9);
lean_inc_ref(v_relManifestFile_664_);
lean_dec_ref(v_self_662_);
v___x_665_ = l_Lake_joinRelative(v_dir_663_, v_relManifestFile_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_666_){
_start:
{
lean_object* v_config_667_; lean_object* v_dir_668_; lean_object* v_buildDir_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_config_667_ = lean_ctor_get(v_self_666_, 6);
lean_inc_ref(v_config_667_);
v_dir_668_ = lean_ctor_get(v_self_666_, 4);
lean_inc_ref(v_dir_668_);
lean_dec_ref(v_self_666_);
v_buildDir_669_ = lean_ctor_get(v_config_667_, 5);
lean_inc_ref(v_buildDir_669_);
lean_dec_ref(v_config_667_);
v___x_670_ = l_System_FilePath_normalize(v_buildDir_669_);
v___x_671_ = l_Lake_joinRelative(v_dir_668_, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_672_){
_start:
{
lean_object* v_config_673_; lean_object* v_testDriverArgs_674_; 
v_config_673_ = lean_ctor_get(v_self_672_, 6);
v_testDriverArgs_674_ = lean_ctor_get(v_config_673_, 13);
lean_inc_ref(v_testDriverArgs_674_);
return v_testDriverArgs_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_Package_testDriverArgs(v_self_675_);
lean_dec_ref(v_self_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_677_){
_start:
{
lean_object* v_config_678_; lean_object* v_lintDriverArgs_679_; 
v_config_678_ = lean_ctor_get(v_self_677_, 6);
v_lintDriverArgs_679_ = lean_ctor_get(v_config_678_, 15);
lean_inc_ref(v_lintDriverArgs_679_);
return v_lintDriverArgs_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lake_Package_lintDriverArgs(v_self_680_);
lean_dec_ref(v_self_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_682_){
_start:
{
lean_object* v_config_683_; lean_object* v_extraDepTargets_684_; 
v_config_683_ = lean_ctor_get(v_self_682_, 6);
v_extraDepTargets_684_ = lean_ctor_get(v_config_683_, 2);
lean_inc_ref(v_extraDepTargets_684_);
return v_extraDepTargets_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lake_Package_extraDepTargets(v_self_685_);
lean_dec_ref(v_self_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_687_){
_start:
{
lean_object* v_config_688_; lean_object* v_toLeanConfig_689_; lean_object* v_platformIndependent_690_; 
v_config_688_ = lean_ctor_get(v_self_687_, 6);
v_toLeanConfig_689_ = lean_ctor_get(v_config_688_, 1);
v_platformIndependent_690_ = lean_ctor_get(v_toLeanConfig_689_, 10);
lean_inc(v_platformIndependent_690_);
return v_platformIndependent_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lake_Package_platformIndependent(v_self_691_);
lean_dec_ref(v_self_691_);
return v_res_692_;
}
}
uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_699_){
_start:
{
lean_object* v_config_700_; lean_object* v_toLeanConfig_701_; lean_object* v_platformIndependent_702_; lean_object* v___f_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_config_700_ = lean_ctor_get(v_self_699_, 6);
lean_inc_ref(v_config_700_);
lean_dec_ref(v_self_699_);
v_toLeanConfig_701_ = lean_ctor_get(v_config_700_, 1);
lean_inc_ref(v_toLeanConfig_701_);
lean_dec_ref(v_config_700_);
v_platformIndependent_702_ = lean_ctor_get(v_toLeanConfig_701_, 10);
lean_inc(v_platformIndependent_702_);
lean_dec_ref(v_toLeanConfig_701_);
v___f_703_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_704_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_705_ = l_instBEqOption_beq___redArg(v___f_703_, v_platformIndependent_702_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lake_Package_isPlatformIndependent_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_699_ = stack[0].m_obj;
uint8_t v_res_706_;
v_res_706_ = l_Lake_Package_isPlatformIndependent(v_self_699_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lake_Package_isPlatformIndependent(v_self_707_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_710_){
_start:
{
lean_object* v_config_711_; uint8_t v_fixedToolchain_712_; 
v_config_711_ = lean_ctor_get(v_self_710_, 6);
v_fixedToolchain_712_ = lean_ctor_get_uint8(v_config_711_, sizeof(void*)*28 + 6);
return v_fixedToolchain_712_;
}
}
LEAN_EXPORT void l_Lake_Package_fixedToolchain_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_710_ = stack[0].m_obj;
uint8_t v_res_713_;
v_res_713_ = l_Lake_Package_fixedToolchain(v_self_710_);
stack->m_num = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lake_Package_fixedToolchain(v_self_714_);
lean_dec_ref(v_self_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_717_){
_start:
{
lean_object* v_config_718_; lean_object* v_releaseRepo_719_; 
v_config_718_ = lean_ctor_get(v_self_717_, 6);
v_releaseRepo_719_ = lean_ctor_get(v_config_718_, 10);
lean_inc(v_releaseRepo_719_);
return v_releaseRepo_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lake_Package_releaseRepo_x3f(v_self_720_);
lean_dec_ref(v_self_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_722_){
_start:
{
lean_object* v_remoteUrl_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_remoteUrl_723_ = lean_ctor_get(v_self_722_, 11);
v___x_724_ = lean_string_utf8_byte_size(v_remoteUrl_723_);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_nat_dec_eq(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_inc_ref(v_remoteUrl_723_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_remoteUrl_723_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_box(0);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lake_Package_remoteUrl_x3f(v_self_729_);
lean_dec_ref(v_self_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_731_){
_start:
{
lean_object* v_dir_732_; lean_object* v_buildArchive_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_dir_732_ = lean_ctor_get(v_self_731_, 4);
lean_inc_ref(v_dir_732_);
v_buildArchive_733_ = lean_ctor_get(v_self_731_, 21);
lean_inc_ref(v_buildArchive_733_);
lean_dec_ref(v_self_731_);
v___x_734_ = l_Lake_defaultLakeDir;
v___x_735_ = l_Lake_joinRelative(v_dir_732_, v___x_734_);
v___x_736_ = l_Lake_joinRelative(v___x_735_, v_buildArchive_733_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_738_){
_start:
{
lean_object* v_dir_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_dir_739_ = lean_ctor_get(v_self_738_, 4);
lean_inc_ref(v_dir_739_);
lean_dec_ref(v_self_738_);
v___x_740_ = l_Lake_defaultLakeDir;
v___x_741_ = l_Lake_joinRelative(v_dir_739_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_743_ = l_Lake_joinRelative(v___x_741_, v___x_742_);
return v___x_743_;
}
}
uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_744_){
_start:
{
lean_object* v_config_745_; uint8_t v_preferReleaseBuild_746_; 
v_config_745_ = lean_ctor_get(v_self_744_, 6);
v_preferReleaseBuild_746_ = lean_ctor_get_uint8(v_config_745_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_746_;
}
}
LEAN_EXPORT void l_Lake_Package_preferReleaseBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_744_ = stack[0].m_obj;
uint8_t v_res_747_;
v_res_747_ = l_Lake_Package_preferReleaseBuild(v_self_744_);
stack->m_num = v_res_747_;
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lake_Package_preferReleaseBuild(v_self_748_);
lean_dec_ref(v_self_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
uint8_t l_Lake_Package_precompileModules(lean_object* v_self_751_){
_start:
{
lean_object* v_config_752_; uint8_t v_precompileModules_753_; 
v_config_752_ = lean_ctor_get(v_self_751_, 6);
v_precompileModules_753_ = lean_ctor_get_uint8(v_config_752_, sizeof(void*)*28 + 1);
return v_precompileModules_753_;
}
}
LEAN_EXPORT void l_Lake_Package_precompileModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_751_ = stack[0].m_obj;
uint8_t v_res_754_;
v_res_754_ = l_Lake_Package_precompileModules(v_self_751_);
stack->m_num = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lake_Package_precompileModules(v_self_755_);
lean_dec_ref(v_self_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
uint8_t l_Lake_Package_precompileImports(lean_object* v_self_758_){
_start:
{
lean_object* v_config_759_; lean_object* v_toLeanConfig_760_; uint8_t v_precompileImports_761_; 
v_config_759_ = lean_ctor_get(v_self_758_, 6);
v_toLeanConfig_760_ = lean_ctor_get(v_config_759_, 1);
v_precompileImports_761_ = lean_ctor_get_uint8(v_toLeanConfig_760_, sizeof(void*)*13 + 2);
return v_precompileImports_761_;
}
}
LEAN_EXPORT void l_Lake_Package_precompileImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_758_ = stack[0].m_obj;
uint8_t v_res_762_;
v_res_762_ = l_Lake_Package_precompileImports(v_self_758_);
stack->m_num = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileImports___boxed(lean_object* v_self_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lake_Package_precompileImports(v_self_763_);
lean_dec_ref(v_self_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_766_){
_start:
{
lean_object* v_config_767_; lean_object* v_moreGlobalServerArgs_768_; 
v_config_767_ = lean_ctor_get(v_self_766_, 6);
v_moreGlobalServerArgs_768_ = lean_ctor_get(v_config_767_, 3);
lean_inc_ref(v_moreGlobalServerArgs_768_);
return v_moreGlobalServerArgs_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_Package_moreGlobalServerArgs(v_self_769_);
lean_dec_ref(v_self_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_771_){
_start:
{
lean_object* v_config_772_; lean_object* v_toLeanConfig_773_; lean_object* v_leanOptions_774_; lean_object* v_moreServerOptions_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_config_772_ = lean_ctor_get(v_self_771_, 6);
v_toLeanConfig_773_ = lean_ctor_get(v_config_772_, 1);
v_leanOptions_774_ = lean_ctor_get(v_toLeanConfig_773_, 0);
v_moreServerOptions_775_ = lean_ctor_get(v_toLeanConfig_773_, 4);
v___x_776_ = l_Lean_LeanOptions_ofArray(v_leanOptions_774_);
v___x_777_ = l_Lean_LeanOptions_appendArray(v___x_776_, v_moreServerOptions_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_Package_moreServerOptions(v_self_778_);
lean_dec_ref(v_self_778_);
return v_res_779_;
}
}
uint8_t l_Lake_Package_buildType(lean_object* v_self_780_){
_start:
{
lean_object* v_config_781_; lean_object* v_toLeanConfig_782_; uint8_t v_buildType_783_; 
v_config_781_ = lean_ctor_get(v_self_780_, 6);
v_toLeanConfig_782_ = lean_ctor_get(v_config_781_, 1);
v_buildType_783_ = lean_ctor_get_uint8(v_toLeanConfig_782_, sizeof(void*)*13);
return v_buildType_783_;
}
}
LEAN_EXPORT void l_Lake_Package_buildType_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_780_ = stack[0].m_obj;
uint8_t v_res_784_;
v_res_784_ = l_Lake_Package_buildType(v_self_780_);
stack->m_num = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lake_Package_buildType(v_self_785_);
lean_dec_ref(v_self_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
uint8_t l_Lake_Package_backend(lean_object* v_self_788_){
_start:
{
lean_object* v_config_789_; lean_object* v_toLeanConfig_790_; uint8_t v_backend_791_; 
v_config_789_ = lean_ctor_get(v_self_788_, 6);
v_toLeanConfig_790_ = lean_ctor_get(v_config_789_, 1);
v_backend_791_ = lean_ctor_get_uint8(v_toLeanConfig_790_, sizeof(void*)*13 + 1);
return v_backend_791_;
}
}
LEAN_EXPORT void l_Lake_Package_backend_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_788_ = stack[0].m_obj;
uint8_t v_res_792_;
v_res_792_ = l_Lake_Package_backend(v_self_788_);
stack->m_num = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Lake_Package_backend(v_self_793_);
lean_dec_ref(v_self_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_796_){
_start:
{
lean_object* v_config_797_; uint8_t v_allowImportAll_798_; 
v_config_797_ = lean_ctor_get(v_self_796_, 6);
v_allowImportAll_798_ = lean_ctor_get_uint8(v_config_797_, sizeof(void*)*28 + 5);
return v_allowImportAll_798_;
}
}
LEAN_EXPORT void l_Lake_Package_allowImportAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_796_ = stack[0].m_obj;
uint8_t v_res_799_;
v_res_799_ = l_Lake_Package_allowImportAll(v_self_796_);
stack->m_num = v_res_799_;
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Lake_Package_allowImportAll(v_self_800_);
lean_dec_ref(v_self_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_803_){
_start:
{
lean_object* v_config_804_; lean_object* v_toLeanConfig_805_; uint8_t v_requiresModuleSystem_806_; 
v_config_804_ = lean_ctor_get(v_self_803_, 6);
v_toLeanConfig_805_ = lean_ctor_get(v_config_804_, 1);
v_requiresModuleSystem_806_ = lean_ctor_get_uint8(v_toLeanConfig_805_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_806_;
}
}
LEAN_EXPORT void l_Lake_Package_requiresModuleSystem_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_803_ = stack[0].m_obj;
uint8_t v_res_807_;
v_res_807_ = l_Lake_Package_requiresModuleSystem(v_self_803_);
stack->m_num = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Lake_Package_requiresModuleSystem(v_self_808_);
lean_dec_ref(v_self_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_811_){
_start:
{
lean_object* v_config_812_; lean_object* v_toLeanConfig_813_; uint8_t v_allowNonModules_814_; 
v_config_812_ = lean_ctor_get(v_self_811_, 6);
v_toLeanConfig_813_ = lean_ctor_get(v_config_812_, 1);
v_allowNonModules_814_ = lean_ctor_get_uint8(v_toLeanConfig_813_, sizeof(void*)*13 + 4);
return v_allowNonModules_814_;
}
}
LEAN_EXPORT void l_Lake_Package_allowNonModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_811_ = stack[0].m_obj;
uint8_t v_res_815_;
v_res_815_ = l_Lake_Package_allowNonModules(v_self_811_);
stack->m_num = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Lake_Package_allowNonModules(v_self_816_);
lean_dec_ref(v_self_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_819_){
_start:
{
lean_object* v_config_820_; lean_object* v_toLeanConfig_821_; lean_object* v_dynlibs_822_; 
v_config_820_ = lean_ctor_get(v_self_819_, 6);
v_toLeanConfig_821_ = lean_ctor_get(v_config_820_, 1);
v_dynlibs_822_ = lean_ctor_get(v_toLeanConfig_821_, 11);
lean_inc_ref(v_dynlibs_822_);
return v_dynlibs_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lake_Package_dynlibs(v_self_823_);
lean_dec_ref(v_self_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_825_){
_start:
{
lean_object* v_config_826_; lean_object* v_toLeanConfig_827_; lean_object* v_plugins_828_; 
v_config_826_ = lean_ctor_get(v_self_825_, 6);
v_toLeanConfig_827_ = lean_ctor_get(v_config_826_, 1);
v_plugins_828_ = lean_ctor_get(v_toLeanConfig_827_, 12);
lean_inc_ref(v_plugins_828_);
return v_plugins_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lake_Package_plugins(v_self_829_);
lean_dec_ref(v_self_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_831_){
_start:
{
lean_object* v_config_832_; lean_object* v_toLeanConfig_833_; lean_object* v_leanOptions_834_; lean_object* v___x_835_; 
v_config_832_ = lean_ctor_get(v_self_831_, 6);
v_toLeanConfig_833_ = lean_ctor_get(v_config_832_, 1);
v_leanOptions_834_ = lean_ctor_get(v_toLeanConfig_833_, 0);
v___x_835_ = l_Lean_LeanOptions_ofArray(v_leanOptions_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_Package_leanOptions(v_self_836_);
lean_dec_ref(v_self_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_838_){
_start:
{
lean_object* v_config_839_; lean_object* v_toLeanConfig_840_; lean_object* v_moreLeanArgs_841_; 
v_config_839_ = lean_ctor_get(v_self_838_, 6);
v_toLeanConfig_840_ = lean_ctor_get(v_config_839_, 1);
v_moreLeanArgs_841_ = lean_ctor_get(v_toLeanConfig_840_, 1);
lean_inc_ref(v_moreLeanArgs_841_);
return v_moreLeanArgs_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lake_Package_moreLeanArgs(v_self_842_);
lean_dec_ref(v_self_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_844_){
_start:
{
lean_object* v_config_845_; lean_object* v_toLeanConfig_846_; lean_object* v_weakLeanArgs_847_; 
v_config_845_ = lean_ctor_get(v_self_844_, 6);
v_toLeanConfig_846_ = lean_ctor_get(v_config_845_, 1);
v_weakLeanArgs_847_ = lean_ctor_get(v_toLeanConfig_846_, 2);
lean_inc_ref(v_weakLeanArgs_847_);
return v_weakLeanArgs_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_Package_weakLeanArgs(v_self_848_);
lean_dec_ref(v_self_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_850_){
_start:
{
lean_object* v_config_851_; lean_object* v_toLeanConfig_852_; lean_object* v_moreLeancArgs_853_; 
v_config_851_ = lean_ctor_get(v_self_850_, 6);
v_toLeanConfig_852_ = lean_ctor_get(v_config_851_, 1);
v_moreLeancArgs_853_ = lean_ctor_get(v_toLeanConfig_852_, 3);
lean_inc_ref(v_moreLeancArgs_853_);
return v_moreLeancArgs_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lake_Package_moreLeancArgs(v_self_854_);
lean_dec_ref(v_self_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_856_){
_start:
{
lean_object* v_config_857_; lean_object* v_toLeanConfig_858_; lean_object* v_weakLeancArgs_859_; 
v_config_857_ = lean_ctor_get(v_self_856_, 6);
v_toLeanConfig_858_ = lean_ctor_get(v_config_857_, 1);
v_weakLeancArgs_859_ = lean_ctor_get(v_toLeanConfig_858_, 5);
lean_inc_ref(v_weakLeancArgs_859_);
return v_weakLeancArgs_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_Package_weakLeancArgs(v_self_860_);
lean_dec_ref(v_self_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_862_){
_start:
{
lean_object* v_config_863_; lean_object* v_toLeanConfig_864_; lean_object* v_moreLinkObjs_865_; 
v_config_863_ = lean_ctor_get(v_self_862_, 6);
v_toLeanConfig_864_ = lean_ctor_get(v_config_863_, 1);
v_moreLinkObjs_865_ = lean_ctor_get(v_toLeanConfig_864_, 6);
lean_inc_ref(v_moreLinkObjs_865_);
return v_moreLinkObjs_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lake_Package_moreLinkObjs(v_self_866_);
lean_dec_ref(v_self_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_868_){
_start:
{
lean_object* v_config_869_; lean_object* v_toLeanConfig_870_; lean_object* v_moreLinkLibs_871_; 
v_config_869_ = lean_ctor_get(v_self_868_, 6);
v_toLeanConfig_870_ = lean_ctor_get(v_config_869_, 1);
v_moreLinkLibs_871_ = lean_ctor_get(v_toLeanConfig_870_, 7);
lean_inc_ref(v_moreLinkLibs_871_);
return v_moreLinkLibs_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lake_Package_moreLinkLibs(v_self_872_);
lean_dec_ref(v_self_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_874_){
_start:
{
lean_object* v_config_875_; lean_object* v_toLeanConfig_876_; lean_object* v_moreLinkArgs_877_; 
v_config_875_ = lean_ctor_get(v_self_874_, 6);
v_toLeanConfig_876_ = lean_ctor_get(v_config_875_, 1);
v_moreLinkArgs_877_ = lean_ctor_get(v_toLeanConfig_876_, 8);
lean_inc_ref(v_moreLinkArgs_877_);
return v_moreLinkArgs_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lake_Package_moreLinkArgs(v_self_878_);
lean_dec_ref(v_self_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_880_){
_start:
{
lean_object* v_config_881_; lean_object* v_toLeanConfig_882_; lean_object* v_weakLinkArgs_883_; 
v_config_881_ = lean_ctor_get(v_self_880_, 6);
v_toLeanConfig_882_ = lean_ctor_get(v_config_881_, 1);
v_weakLinkArgs_883_ = lean_ctor_get(v_toLeanConfig_882_, 9);
lean_inc_ref(v_weakLinkArgs_883_);
return v_weakLinkArgs_883_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lake_Package_weakLinkArgs(v_self_884_);
lean_dec_ref(v_self_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_886_){
_start:
{
lean_object* v_config_887_; lean_object* v_dir_888_; lean_object* v_srcDir_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_config_887_ = lean_ctor_get(v_self_886_, 6);
lean_inc_ref(v_config_887_);
v_dir_888_ = lean_ctor_get(v_self_886_, 4);
lean_inc_ref(v_dir_888_);
lean_dec_ref(v_self_886_);
v_srcDir_889_ = lean_ctor_get(v_config_887_, 4);
lean_inc_ref(v_srcDir_889_);
lean_dec_ref(v_config_887_);
v___x_890_ = l_System_FilePath_normalize(v_srcDir_889_);
v___x_891_ = l_Lake_joinRelative(v_dir_888_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_892_){
_start:
{
lean_object* v_config_893_; lean_object* v_dir_894_; lean_object* v_srcDir_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_config_893_ = lean_ctor_get(v_self_892_, 6);
lean_inc_ref(v_config_893_);
v_dir_894_ = lean_ctor_get(v_self_892_, 4);
lean_inc_ref(v_dir_894_);
lean_dec_ref(v_self_892_);
v_srcDir_895_ = lean_ctor_get(v_config_893_, 4);
lean_inc_ref(v_srcDir_895_);
lean_dec_ref(v_config_893_);
v___x_896_ = l_System_FilePath_normalize(v_srcDir_895_);
v___x_897_ = l_Lake_joinRelative(v_dir_894_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_898_){
_start:
{
lean_object* v_config_899_; lean_object* v_dir_900_; lean_object* v_buildDir_901_; lean_object* v_leanLibDir_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_config_899_ = lean_ctor_get(v_self_898_, 6);
lean_inc_ref(v_config_899_);
v_dir_900_ = lean_ctor_get(v_self_898_, 4);
lean_inc_ref(v_dir_900_);
lean_dec_ref(v_self_898_);
v_buildDir_901_ = lean_ctor_get(v_config_899_, 5);
lean_inc_ref(v_buildDir_901_);
v_leanLibDir_902_ = lean_ctor_get(v_config_899_, 6);
lean_inc_ref(v_leanLibDir_902_);
lean_dec_ref(v_config_899_);
v___x_903_ = l_System_FilePath_normalize(v_buildDir_901_);
v___x_904_ = l_Lake_joinRelative(v_dir_900_, v___x_903_);
v___x_905_ = l_System_FilePath_normalize(v_leanLibDir_902_);
v___x_906_ = l_Lake_joinRelative(v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object* v_self_908_){
_start:
{
lean_object* v_config_909_; lean_object* v_dir_910_; lean_object* v_buildDir_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_config_909_ = lean_ctor_get(v_self_908_, 6);
lean_inc_ref(v_config_909_);
v_dir_910_ = lean_ctor_get(v_self_908_, 4);
lean_inc_ref(v_dir_910_);
lean_dec_ref(v_self_908_);
v_buildDir_911_ = lean_ctor_get(v_config_909_, 5);
lean_inc_ref(v_buildDir_911_);
lean_dec_ref(v_config_909_);
v___x_912_ = l_System_FilePath_normalize(v_buildDir_911_);
v___x_913_ = l_Lake_joinRelative(v_dir_910_, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lake_Package_bootstrapIncludeDir___closed__0));
v___x_915_ = l_Lake_joinRelative(v___x_913_, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_916_){
_start:
{
lean_object* v_config_917_; lean_object* v_dir_918_; lean_object* v_buildDir_919_; lean_object* v_nativeLibDir_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_config_917_ = lean_ctor_get(v_self_916_, 6);
lean_inc_ref(v_config_917_);
v_dir_918_ = lean_ctor_get(v_self_916_, 4);
lean_inc_ref(v_dir_918_);
lean_dec_ref(v_self_916_);
v_buildDir_919_ = lean_ctor_get(v_config_917_, 5);
lean_inc_ref(v_buildDir_919_);
v_nativeLibDir_920_ = lean_ctor_get(v_config_917_, 7);
lean_inc_ref(v_nativeLibDir_920_);
lean_dec_ref(v_config_917_);
v___x_921_ = l_System_FilePath_normalize(v_buildDir_919_);
v___x_922_ = l_Lake_joinRelative(v_dir_918_, v___x_921_);
v___x_923_ = l_System_FilePath_normalize(v_nativeLibDir_920_);
v___x_924_ = l_Lake_joinRelative(v___x_922_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_925_){
_start:
{
lean_object* v_config_926_; lean_object* v_dir_927_; lean_object* v_buildDir_928_; lean_object* v_nativeLibDir_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_config_926_ = lean_ctor_get(v_self_925_, 6);
lean_inc_ref(v_config_926_);
v_dir_927_ = lean_ctor_get(v_self_925_, 4);
lean_inc_ref(v_dir_927_);
lean_dec_ref(v_self_925_);
v_buildDir_928_ = lean_ctor_get(v_config_926_, 5);
lean_inc_ref(v_buildDir_928_);
v_nativeLibDir_929_ = lean_ctor_get(v_config_926_, 7);
lean_inc_ref(v_nativeLibDir_929_);
lean_dec_ref(v_config_926_);
v___x_930_ = l_System_FilePath_normalize(v_buildDir_928_);
v___x_931_ = l_Lake_joinRelative(v_dir_927_, v___x_930_);
v___x_932_ = l_System_FilePath_normalize(v_nativeLibDir_929_);
v___x_933_ = l_Lake_joinRelative(v___x_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_934_){
_start:
{
lean_object* v_config_935_; lean_object* v_dir_936_; lean_object* v_buildDir_937_; lean_object* v_binDir_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_config_935_ = lean_ctor_get(v_self_934_, 6);
lean_inc_ref(v_config_935_);
v_dir_936_ = lean_ctor_get(v_self_934_, 4);
lean_inc_ref(v_dir_936_);
lean_dec_ref(v_self_934_);
v_buildDir_937_ = lean_ctor_get(v_config_935_, 5);
lean_inc_ref(v_buildDir_937_);
v_binDir_938_ = lean_ctor_get(v_config_935_, 8);
lean_inc_ref(v_binDir_938_);
lean_dec_ref(v_config_935_);
v___x_939_ = l_System_FilePath_normalize(v_buildDir_937_);
v___x_940_ = l_Lake_joinRelative(v_dir_936_, v___x_939_);
v___x_941_ = l_System_FilePath_normalize(v_binDir_938_);
v___x_942_ = l_Lake_joinRelative(v___x_940_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_943_){
_start:
{
lean_object* v_config_944_; lean_object* v_dir_945_; lean_object* v_buildDir_946_; lean_object* v_irDir_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_config_944_ = lean_ctor_get(v_self_943_, 6);
lean_inc_ref(v_config_944_);
v_dir_945_ = lean_ctor_get(v_self_943_, 4);
lean_inc_ref(v_dir_945_);
lean_dec_ref(v_self_943_);
v_buildDir_946_ = lean_ctor_get(v_config_944_, 5);
lean_inc_ref(v_buildDir_946_);
v_irDir_947_ = lean_ctor_get(v_config_944_, 9);
lean_inc_ref(v_irDir_947_);
lean_dec_ref(v_config_944_);
v___x_948_ = l_System_FilePath_normalize(v_buildDir_946_);
v___x_949_ = l_Lake_joinRelative(v_dir_945_, v___x_948_);
v___x_950_ = l_System_FilePath_normalize(v_irDir_947_);
v___x_951_ = l_Lake_joinRelative(v___x_949_, v___x_950_);
return v___x_951_;
}
}
uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_952_){
_start:
{
lean_object* v_config_953_; uint8_t v_libPrefixOnWindows_954_; 
v_config_953_ = lean_ctor_get(v_self_952_, 6);
v_libPrefixOnWindows_954_ = lean_ctor_get_uint8(v_config_953_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_954_;
}
}
LEAN_EXPORT void l_Lake_Package_libPrefixOnWindows_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_952_ = stack[0].m_obj;
uint8_t v_res_955_;
v_res_955_ = l_Lake_Package_libPrefixOnWindows(v_self_952_);
stack->m_num = v_res_955_;
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_956_){
_start:
{
uint8_t v_res_957_; lean_object* v_r_958_; 
v_res_957_ = l_Lake_Package_libPrefixOnWindows(v_self_956_);
lean_dec_ref(v_self_956_);
v_r_958_ = lean_box(v_res_957_);
return v_r_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_959_){
_start:
{
lean_object* v_config_960_; lean_object* v_enableArtifactCache_x3f_961_; 
v_config_960_ = lean_ctor_get(v_self_959_, 6);
v_enableArtifactCache_x3f_961_ = lean_ctor_get(v_config_960_, 24);
lean_inc(v_enableArtifactCache_x3f_961_);
return v_enableArtifactCache_x3f_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lake_Package_enableArtifactCache_x3f(v_self_962_);
lean_dec_ref(v_self_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_964_){
_start:
{
lean_object* v_config_965_; lean_object* v_restoreAllArtifacts_x3f_966_; 
v_config_965_ = lean_ctor_get(v_self_964_, 6);
v_restoreAllArtifacts_x3f_966_ = lean_ctor_get(v_config_965_, 25);
lean_inc(v_restoreAllArtifacts_x3f_966_);
return v_restoreAllArtifacts_x3f_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_967_);
lean_dec_ref(v_self_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_969_){
_start:
{
lean_object* v_baseName_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v_baseName_970_ = lean_ctor_get(v_self_969_, 1);
lean_inc(v_baseName_970_);
lean_dec_ref(v_self_969_);
v___x_971_ = 0;
v___x_972_ = l_Lean_Name_toString(v_baseName_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_974_){
_start:
{
lean_object* v_origName_975_; lean_object* v_scope_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_origName_975_ = lean_ctor_get(v_self_974_, 3);
lean_inc(v_origName_975_);
v_scope_976_ = lean_ctor_get(v_self_974_, 10);
lean_inc_ref(v_scope_976_);
lean_dec_ref(v_self_974_);
v___x_977_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_978_ = lean_string_append(v_scope_976_, v___x_977_);
v___x_979_ = 0;
v___x_980_ = l_Lean_Name_toString(v_origName_975_, v___x_979_);
v___x_981_ = lean_string_append(v___x_978_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = l_Lake_CacheServiceScope_ofString(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_983_){
_start:
{
lean_object* v_scope_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_scope_984_ = lean_ctor_get(v_self_983_, 10);
v___x_985_ = lean_string_utf8_byte_size(v_scope_984_);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_nat_dec_eq(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_983_);
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v_self_983_);
v___x_990_ = lean_box(0);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_991_, lean_object* v_k_992_){
_start:
{
if (lean_obj_tag(v_t_991_) == 0)
{
lean_object* v_k_993_; lean_object* v_v_994_; lean_object* v_l_995_; lean_object* v_r_996_; uint8_t v___x_997_; 
v_k_993_ = lean_ctor_get(v_t_991_, 1);
v_v_994_ = lean_ctor_get(v_t_991_, 2);
v_l_995_ = lean_ctor_get(v_t_991_, 3);
v_r_996_ = lean_ctor_get(v_t_991_, 4);
v___x_997_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_992_, v_k_993_);
switch(v___x_997_)
{
case 0:
{
v_t_991_ = v_l_995_;
goto _start;
}
case 1:
{
lean_object* v___x_999_; 
lean_inc(v_v_994_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v_v_994_);
return v___x_999_;
}
default: 
{
v_t_991_ = v_r_996_;
goto _start;
}
}
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_1002_, lean_object* v_k_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1002_, v_k_1003_);
lean_dec(v_k_1003_);
lean_dec(v_t_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_1005_, lean_object* v_self_1006_){
_start:
{
lean_object* v_targetDeclMap_1007_; lean_object* v___x_1008_; 
v_targetDeclMap_1007_ = lean_ctor_get(v_self_1006_, 16);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_1007_, v_name_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_1009_, lean_object* v_self_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lake_Package_findTargetDecl_x3f(v_name_1009_, v_self_1010_);
lean_dec_ref(v_self_1010_);
lean_dec(v_name_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_t_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1014_, v_k_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_t_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_1017_, v_inst_1018_, v_t_1019_, v_k_1020_);
lean_dec(v_k_1020_);
lean_dec(v_t_1019_);
return v_res_1021_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v_kind_1031_; lean_object* v_config_1032_; uint8_t v___x_1033_; uint8_t v___y_1035_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1030_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
v_kind_1031_ = lean_ctor_get(v___x_1030_, 2);
v_config_1032_ = lean_ctor_get(v___x_1030_, 3);
v___x_1033_ = 1;
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1040_ = lean_name_eq(v_kind_1031_, v___x_1039_);
if (v___x_1040_ == 0)
{
v___y_1035_ = v___x_1040_;
goto v___jp_1034_;
}
else
{
uint8_t v___x_1041_; 
v___x_1041_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1025_, v_config_1032_);
v___y_1035_ = v___x_1041_;
goto v___jp_1034_;
}
v___jp_1034_:
{
if (v___y_1035_ == 0)
{
size_t v___x_1036_; size_t v___x_1037_; 
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1027_, v___x_1036_);
v_i_1027_ = v___x_1037_;
goto _start;
}
else
{
return v___x_1033_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1025_ = stack[0].m_obj;
lean_object* v_as_1026_ = stack[1].m_obj;
size_t v_i_1027_ = stack[2].m_num;
size_t v_stop_1028_ = stack[3].m_num;
uint8_t v_res_1043_;
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1025_, v_as_1026_, v_i_1027_, v_stop_1028_);
stack->m_num = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_1044_, lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v_stop_1047_){
_start:
{
size_t v_i_boxed_1048_; size_t v_stop_boxed_1049_; uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_i_boxed_1048_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_stop_boxed_1049_ = lean_unbox_usize(v_stop_1047_);
lean_dec(v_stop_1047_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1044_, v_as_1045_, v_i_boxed_1048_, v_stop_boxed_1049_);
lean_dec_ref(v_as_1045_);
lean_dec(v_mod_1044_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_1052_, lean_object* v_self_1053_){
_start:
{
lean_object* v_targetDecls_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_targetDecls_1054_ = lean_ctor_get(v_self_1053_, 15);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_array_get_size(v_targetDecls_1054_);
v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
return v___x_1057_;
}
else
{
if (v___x_1057_ == 0)
{
return v___x_1057_;
}
else
{
size_t v___x_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = lean_usize_of_nat(v___x_1056_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1052_, v_targetDecls_1054_, v___x_1058_, v___x_1059_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT void l_Lake_Package_isLocalModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1052_ = stack[0].m_obj;
lean_object* v_self_1053_ = stack[1].m_obj;
uint8_t v_res_1061_;
v_res_1061_ = l_Lake_Package_isLocalModule(v_mod_1052_, v_self_1053_);
stack->m_num = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1062_, lean_object* v_self_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lake_Package_isLocalModule(v_mod_1062_, v_self_1063_);
lean_dec_ref(v_self_1063_);
lean_dec(v_mod_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1066_, lean_object* v_as_1067_, size_t v_i_1068_, size_t v_stop_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_eq(v_i_1068_, v_stop_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v_kind_1072_; lean_object* v_config_1073_; uint8_t v___x_1074_; uint8_t v___y_1076_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1071_ = lean_array_uget_borrowed(v_as_1067_, v_i_1068_);
v_kind_1072_ = lean_ctor_get(v___x_1071_, 2);
v_config_1073_ = lean_ctor_get(v___x_1071_, 3);
v___x_1074_ = 1;
v___x_1087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1088_ = lean_name_eq(v_kind_1072_, v___x_1087_);
if (v___x_1088_ == 0)
{
goto v___jp_1080_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1066_, v_config_1073_);
if (v___x_1089_ == 0)
{
goto v___jp_1080_;
}
else
{
v___y_1076_ = v___x_1089_;
goto v___jp_1075_;
}
}
v___jp_1075_:
{
if (v___y_1076_ == 0)
{
size_t v___x_1077_; size_t v___x_1078_; 
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1068_, v___x_1077_);
v_i_1068_ = v___x_1078_;
goto _start;
}
else
{
return v___x_1074_;
}
}
v___jp_1080_:
{
lean_object* v_kind_1081_; lean_object* v_config_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_kind_1081_ = lean_ctor_get(v___x_1071_, 2);
v_config_1082_ = lean_ctor_get(v___x_1071_, 3);
v___x_1083_ = l_Lake_LeanExe_keyword;
v___x_1084_ = lean_name_eq(v_kind_1081_, v___x_1083_);
if (v___x_1084_ == 0)
{
v___y_1076_ = v___x_1084_;
goto v___jp_1075_;
}
else
{
lean_object* v_root_1085_; uint8_t v___x_1086_; 
v_root_1085_ = lean_ctor_get(v_config_1082_, 2);
v___x_1086_ = lean_name_eq(v_root_1085_, v_mod_1066_);
v___y_1076_ = v___x_1086_;
goto v___jp_1075_;
}
}
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = 0;
return v___x_1090_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1066_ = stack[0].m_obj;
lean_object* v_as_1067_ = stack[1].m_obj;
size_t v_i_1068_ = stack[2].m_num;
size_t v_stop_1069_ = stack[3].m_num;
uint8_t v_res_1091_;
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1066_, v_as_1067_, v_i_1068_, v_stop_1069_);
stack->m_num = v_res_1091_;
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
uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1100_, lean_object* v_self_1101_){
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
LEAN_EXPORT void l_Lake_Package_isBuildableModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1100_ = stack[0].m_obj;
lean_object* v_self_1101_ = stack[1].m_obj;
uint8_t v_res_1109_;
v_res_1109_ = l_Lake_Package_isBuildableModule(v_mod_1100_, v_self_1101_);
stack->m_num = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1110_, lean_object* v_self_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l_Lake_Package_isBuildableModule(v_mod_1110_, v_self_1111_);
lean_dec_ref(v_self_1111_);
lean_dec(v_mod_1110_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
lean_object* l_Lake_Package_clean(lean_object* v_self_1114_){
_start:
{
lean_object* v_config_1116_; lean_object* v_dir_1117_; lean_object* v_buildDir_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_config_1116_ = lean_ctor_get(v_self_1114_, 6);
lean_inc_ref(v_config_1116_);
v_dir_1117_ = lean_ctor_get(v_self_1114_, 4);
lean_inc_ref(v_dir_1117_);
lean_dec_ref(v_self_1114_);
v_buildDir_1118_ = lean_ctor_get(v_config_1116_, 5);
lean_inc_ref(v_buildDir_1118_);
lean_dec_ref(v_config_1116_);
v___x_1119_ = l_System_FilePath_normalize(v_buildDir_1118_);
v___x_1120_ = l_Lake_joinRelative(v_dir_1117_, v___x_1119_);
v___x_1121_ = l_Lake_removeDirAllIfExists(v___x_1120_);
lean_dec_ref(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT void l_Lake_Package_clean_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1114_ = stack[0].m_obj;
lean_object* v_res_1122_;
v_res_1122_ = l_Lake_Package_clean(v_self_1114_);
stack->m_obj
 = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lake_Package_clean(v_self_1123_);
return v_res_1125_;
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
