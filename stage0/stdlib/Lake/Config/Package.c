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
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
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
lean_inc(v_size_24_);
v_k_25_ = lean_ctor_get(v_impl_21_, 1);
lean_inc(v_k_25_);
v_v_26_ = lean_ctor_get(v_impl_21_, 2);
lean_inc(v_v_26_);
v_l_27_ = lean_ctor_get(v_impl_21_, 3);
lean_inc(v_l_27_);
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
lean_dec(v_l_27_);
lean_dec(v_v_26_);
lean_dec(v_k_25_);
v___x_32_ = lean_nat_add(v___x_22_, v_size_24_);
lean_dec(v_size_24_);
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
lean_inc(v_l_108_);
if (lean_obj_tag(v_l_108_) == 0)
{
lean_object* v_r_109_; lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
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
lean_inc(v_size_164_);
v_k_165_ = lean_ctor_get(v_impl_161_, 1);
lean_inc(v_k_165_);
v_v_166_ = lean_ctor_get(v_impl_161_, 2);
lean_inc(v_v_166_);
v_l_167_ = lean_ctor_get(v_impl_161_, 3);
lean_inc(v_l_167_);
v_r_168_ = lean_ctor_get(v_impl_161_, 4);
lean_inc(v_r_168_);
v___x_169_ = lean_unsigned_to_nat(3u);
v___x_170_ = lean_nat_mul(v___x_169_, v_size_163_);
v___x_171_ = lean_nat_dec_lt(v___x_170_, v_size_164_);
lean_dec(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec(v_r_168_);
lean_dec(v_l_167_);
lean_dec(v_v_166_);
lean_dec(v_k_165_);
v___x_172_ = lean_nat_add(v___x_162_, v_size_163_);
v___x_173_ = lean_nat_add(v___x_172_, v_size_164_);
lean_dec(v_size_164_);
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
static uint8_t _init_l_Lake_instInhabitedPackage_default___closed__12(void){
_start:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_344_ = lean_nat_dec_le(v___x_343_, v___x_343_);
return v___x_344_;
}
}
static size_t _init_l_Lake_instInhabitedPackage_default___closed__13(void){
_start:
{
lean_object* v___x_345_; size_t v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__10, &l_Lake_instInhabitedPackage_default___closed__10_once, _init_l_Lake_instInhabitedPackage_default___closed__10);
v___x_346_ = lean_usize_of_nat(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__14(void){
_start:
{
lean_object* v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_347_ = lean_box(1);
v___x_348_ = lean_usize_once(&l_Lake_instInhabitedPackage_default___closed__13, &l_Lake_instInhabitedPackage_default___closed__13_once, _init_l_Lake_instInhabitedPackage_default___closed__13);
v___x_349_ = ((size_t)0ULL);
v___x_350_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v___x_350_, v___x_349_, v___x_348_, v___x_347_);
return v___x_351_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_369_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_box(0);
v___x_354_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_355_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_356_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__2, &l_Lake_instInhabitedPackage_default___closed__2_once, _init_l_Lake_instInhabitedPackage_default___closed__2);
v___x_357_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_374_ = lean_box(1);
v___x_375_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__11, &l_Lake_instInhabitedPackage_default___closed__11_once, _init_l_Lake_instInhabitedPackage_default___closed__11);
if (v___x_375_ == 0)
{
v___y_369_ = v___x_374_;
goto v___jp_368_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = lean_uint8_once(&l_Lake_instInhabitedPackage_default___closed__12, &l_Lake_instInhabitedPackage_default___closed__12_once, _init_l_Lake_instInhabitedPackage_default___closed__12);
if (v___x_376_ == 0)
{
if (v___x_375_ == 0)
{
v___y_369_ = v___x_374_;
goto v___jp_368_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_369_ = v___x_377_;
goto v___jp_368_;
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__14, &l_Lake_instInhabitedPackage_default___closed__14_once, _init_l_Lake_instInhabitedPackage_default___closed__14);
v___y_369_ = v___x_378_;
goto v___jp_368_;
}
}
v___jp_358_:
{
lean_object* v_testDriver_365_; lean_object* v_lintDriver_366_; lean_object* v___x_367_; 
v_testDriver_365_ = lean_ctor_get(v___x_356_, 12);
v_lintDriver_366_ = lean_ctor_get(v___x_356_, 14);
lean_inc_ref(v_lintDriver_366_);
lean_inc_ref(v_testDriver_365_);
lean_inc_ref(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_362_);
lean_inc(v___y_359_);
v___x_367_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v___x_367_, 0, v___x_352_);
lean_ctor_set(v___x_367_, 1, v___x_353_);
lean_ctor_set(v___x_367_, 2, v___x_354_);
lean_ctor_set(v___x_367_, 3, v___x_353_);
lean_ctor_set(v___x_367_, 4, v___x_355_);
lean_ctor_set(v___x_367_, 5, v___x_355_);
lean_ctor_set(v___x_367_, 6, v___x_356_);
lean_ctor_set(v___x_367_, 7, v___x_355_);
lean_ctor_set(v___x_367_, 8, v___x_355_);
lean_ctor_set(v___x_367_, 9, v___x_355_);
lean_ctor_set(v___x_367_, 10, v___x_355_);
lean_ctor_set(v___x_367_, 11, v___x_355_);
lean_ctor_set(v___x_367_, 12, v___x_357_);
lean_ctor_set(v___x_367_, 13, v___x_357_);
lean_ctor_set(v___x_367_, 14, v___x_357_);
lean_ctor_set(v___x_367_, 15, v___x_357_);
lean_ctor_set(v___x_367_, 16, v___y_359_);
lean_ctor_set(v___x_367_, 17, v___y_362_);
lean_ctor_set(v___x_367_, 18, v___y_361_);
lean_ctor_set(v___x_367_, 19, v___y_360_);
lean_ctor_set(v___x_367_, 20, v___y_363_);
lean_ctor_set(v___x_367_, 21, v___y_364_);
lean_ctor_set(v___x_367_, 22, v_testDriver_365_);
lean_ctor_set(v___x_367_, 23, v_lintDriver_366_);
return v___x_367_;
}
v___jp_368_:
{
lean_object* v_buildArchive_370_; lean_object* v___x_371_; 
v_buildArchive_370_ = lean_ctor_get(v___x_356_, 11);
v___x_371_ = lean_box(1);
if (lean_obj_tag(v_buildArchive_370_) == 1)
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v_buildArchive_370_, 0);
v___y_359_ = v___y_369_;
v___y_360_ = v___x_357_;
v___y_361_ = v___x_371_;
v___y_362_ = v___x_357_;
v___y_363_ = v___x_357_;
v___y_364_ = v_val_372_;
goto v___jp_358_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__9, &l_Lake_instInhabitedPackage_default___closed__9_once, _init_l_Lake_instInhabitedPackage_default___closed__9);
v___y_359_ = v___y_369_;
v___y_360_ = v___x_357_;
v___y_361_ = v___x_371_;
v___y_362_ = v___x_357_;
v___y_363_ = v___x_357_;
v___y_364_ = v___x_373_;
goto v___jp_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(lean_object* v_00_u03b2_379_, lean_object* v_k_380_, lean_object* v_v_381_, lean_object* v_t_382_, lean_object* v_hl_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_380_, v_v_381_, v_t_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lake_instInhabitedPackage_default;
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
v___x_388_ = 1723ULL;
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
lean_object* v___x_438_; 
v___x_438_ = l_Lake_OrdHashSet_empty___redArg();
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
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(lean_object* v_self_440_){
_start:
{
lean_inc_ref(v_self_440_);
return v_self_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___lam__0___boxed(lean_object* v_self_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lake_NPackage_instCoeOutPackage___redArg___lam__0(v_self_441_);
lean_dec_ref(v_self_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg(){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___redArg___boxed(lean_object* v___dummy_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_NPackage_instCoeOutPackage___redArg();
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_448_){
_start:
{
lean_object* v___f_449_; 
v___f_449_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___redArg___closed__0));
return v___f_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_NPackage_instCoeOutPackage(v_n_450_);
lean_dec(v_n_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_452_){
_start:
{
lean_inc_ref(v_pkg_452_);
return v_pkg_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_453_);
lean_dec_ref(v_pkg_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(lean_object* v_x_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___y_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0___boxed(lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_instInhabitedPostUpdateHook_default___redArg___lam__0(v_x_461_, v___y_462_, v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v_x_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg(){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___redArg___boxed(lean_object* v___dummy_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lake_instInhabitedPostUpdateHook_default___redArg();
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_471_){
_start:
{
lean_object* v___f_472_; 
v___f_472_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_473_);
lean_dec(v_pkgName_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg(){
_start:
{
lean_object* v___f_476_; 
v___f_476_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___redArg___boxed(lean_object* v___dummy_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_instInhabitedPostUpdateHook___redArg();
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_479_){
_start:
{
lean_object* v___f_480_; 
v___f_480_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___redArg___closed__0));
return v___f_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lake_instInhabitedPostUpdateHook(v_a_481_);
lean_dec(v_a_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_483_){
_start:
{
lean_inc_ref(v_a_483_);
return v_a_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_484_);
lean_dec_ref(v_a_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_486_, lean_object* v_a_487_){
_start:
{
lean_inc_ref(v_a_487_);
return v_a_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_488_, v_a_489_);
lean_dec_ref(v_a_489_);
lean_dec(v_name_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_492_, 0, v_name_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_493_){
_start:
{
lean_inc(v_a_493_);
return v_a_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_494_);
lean_dec(v_a_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_496_, lean_object* v_a_497_){
_start:
{
lean_inc(v_a_497_);
return v_a_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec(v_name_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_502_, 0, v_name_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_503_){
_start:
{
lean_inc_ref(v_inst_503_);
return v_inst_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_504_);
lean_dec_ref(v_inst_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_506_, lean_object* v_inst_507_){
_start:
{
lean_inc_ref(v_inst_507_);
return v_inst_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_508_, lean_object* v_inst_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_508_, v_inst_509_);
lean_dec_ref(v_inst_509_);
lean_dec(v_name_508_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_518_){
_start:
{
lean_object* v_wsIdx_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_wsIdx_519_ = lean_ctor_get(v_self_518_, 0);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v_wsIdx_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Lake_Package_isRoot(v_self_522_);
lean_dec_ref(v_self_522_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_525_){
_start:
{
lean_object* v_config_526_; uint8_t v_bootstrap_527_; 
v_config_526_ = lean_ctor_get(v_self_525_, 6);
v_bootstrap_527_ = lean_ctor_get_uint8(v_config_526_, sizeof(void*)*28);
return v_bootstrap_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Lake_Package_bootstrap(v_self_528_);
lean_dec_ref(v_self_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_531_){
_start:
{
lean_object* v_config_532_; uint8_t v_bootstrap_533_; 
v_config_532_ = lean_ctor_get(v_self_531_, 6);
v_bootstrap_533_ = lean_ctor_get_uint8(v_config_532_, sizeof(void*)*28);
if (v_bootstrap_533_ == 0)
{
lean_object* v_origName_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_origName_534_ = lean_ctor_get(v_self_531_, 3);
lean_inc(v_origName_534_);
lean_dec_ref(v_self_531_);
v___x_535_ = l_Lean_Name_toString(v_origName_534_, v_bootstrap_533_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
lean_dec_ref(v_self_531_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_538_){
_start:
{
lean_object* v_config_539_; lean_object* v_version_540_; 
v_config_539_ = lean_ctor_get(v_self_538_, 6);
v_version_540_ = lean_ctor_get(v_config_539_, 16);
lean_inc_ref(v_version_540_);
return v_version_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lake_Package_version(v_self_541_);
lean_dec_ref(v_self_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_543_){
_start:
{
lean_object* v_config_544_; lean_object* v_versionTags_545_; 
v_config_544_ = lean_ctor_get(v_self_543_, 6);
v_versionTags_545_ = lean_ctor_get(v_config_544_, 17);
lean_inc_ref(v_versionTags_545_);
return v_versionTags_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lake_Package_versionTags(v_self_546_);
lean_dec_ref(v_self_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_548_){
_start:
{
lean_object* v_config_549_; lean_object* v_description_550_; 
v_config_549_ = lean_ctor_get(v_self_548_, 6);
v_description_550_ = lean_ctor_get(v_config_549_, 18);
lean_inc_ref(v_description_550_);
return v_description_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lake_Package_description(v_self_551_);
lean_dec_ref(v_self_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_553_){
_start:
{
lean_object* v_config_554_; lean_object* v_keywords_555_; 
v_config_554_ = lean_ctor_get(v_self_553_, 6);
v_keywords_555_ = lean_ctor_get(v_config_554_, 19);
lean_inc_ref(v_keywords_555_);
return v_keywords_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_Package_keywords(v_self_556_);
lean_dec_ref(v_self_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_558_){
_start:
{
lean_object* v_config_559_; lean_object* v_homepage_560_; 
v_config_559_ = lean_ctor_get(v_self_558_, 6);
v_homepage_560_ = lean_ctor_get(v_config_559_, 20);
lean_inc_ref(v_homepage_560_);
return v_homepage_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_Package_homepage(v_self_561_);
lean_dec_ref(v_self_561_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_563_){
_start:
{
lean_object* v_config_564_; uint8_t v_reservoir_565_; 
v_config_564_ = lean_ctor_get(v_self_563_, 6);
v_reservoir_565_ = lean_ctor_get_uint8(v_config_564_, sizeof(void*)*28 + 3);
return v_reservoir_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Lake_Package_reservoir(v_self_566_);
lean_dec_ref(v_self_566_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_569_){
_start:
{
lean_object* v_config_570_; lean_object* v_license_571_; 
v_config_570_ = lean_ctor_get(v_self_569_, 6);
v_license_571_ = lean_ctor_get(v_config_570_, 21);
lean_inc_ref(v_license_571_);
return v_license_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lake_Package_license(v_self_572_);
lean_dec_ref(v_self_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_594_){
_start:
{
lean_object* v_config_595_; lean_object* v_licenseFiles_596_; lean_object* v___f_597_; lean_object* v___x_598_; size_t v_sz_599_; size_t v___x_600_; lean_object* v___x_601_; 
v_config_595_ = lean_ctor_get(v_self_594_, 6);
lean_inc_ref(v_config_595_);
lean_dec_ref(v_self_594_);
v_licenseFiles_596_ = lean_ctor_get(v_config_595_, 22);
lean_inc_ref(v_licenseFiles_596_);
lean_dec_ref(v_config_595_);
v___f_597_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_598_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_599_ = lean_array_size(v_licenseFiles_596_);
v___x_600_ = ((size_t)0ULL);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_598_, v___f_597_, v_sz_599_, v___x_600_, v_licenseFiles_596_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_System_FilePath_normalize(v_x_603_);
v___x_605_ = l_Lake_joinRelative(v_dir_602_, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_606_){
_start:
{
lean_object* v_config_607_; lean_object* v_dir_608_; lean_object* v_licenseFiles_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_612_; size_t v_sz_613_; size_t v___x_614_; lean_object* v___x_615_; size_t v_sz_616_; lean_object* v___x_617_; 
v_config_607_ = lean_ctor_get(v_self_606_, 6);
lean_inc_ref(v_config_607_);
v_dir_608_ = lean_ctor_get(v_self_606_, 4);
lean_inc_ref(v_dir_608_);
lean_dec_ref(v_self_606_);
v_licenseFiles_609_ = lean_ctor_get(v_config_607_, 22);
lean_inc_ref(v_licenseFiles_609_);
lean_dec_ref(v_config_607_);
v___f_610_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_611_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_611_, 0, v_dir_608_);
v___x_612_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_613_ = lean_array_size(v_licenseFiles_609_);
v___x_614_ = ((size_t)0ULL);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_612_, v___f_610_, v_sz_613_, v___x_614_, v_licenseFiles_609_);
v_sz_616_ = lean_array_size(v___x_615_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_612_, v___f_611_, v_sz_616_, v___x_614_, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_618_){
_start:
{
lean_object* v_config_619_; lean_object* v_readmeFile_620_; lean_object* v___x_621_; 
v_config_619_ = lean_ctor_get(v_self_618_, 6);
lean_inc_ref(v_config_619_);
lean_dec_ref(v_self_618_);
v_readmeFile_620_ = lean_ctor_get(v_config_619_, 23);
lean_inc_ref(v_readmeFile_620_);
lean_dec_ref(v_config_619_);
v___x_621_ = l_System_FilePath_normalize(v_readmeFile_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_622_){
_start:
{
lean_object* v_config_623_; lean_object* v_dir_624_; lean_object* v_readmeFile_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_config_623_ = lean_ctor_get(v_self_622_, 6);
lean_inc_ref(v_config_623_);
v_dir_624_ = lean_ctor_get(v_self_622_, 4);
lean_inc_ref(v_dir_624_);
lean_dec_ref(v_self_622_);
v_readmeFile_625_ = lean_ctor_get(v_config_623_, 23);
lean_inc_ref(v_readmeFile_625_);
lean_dec_ref(v_config_623_);
v___x_626_ = l_System_FilePath_normalize(v_readmeFile_625_);
v___x_627_ = l_Lake_joinRelative(v_dir_624_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg(){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lake_defaultLakeDir;
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___redArg___boxed(lean_object* v___dummy_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lake_Package_relLakeDir___redArg();
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lake_defaultLakeDir;
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lake_Package_relLakeDir(v_x_634_);
lean_dec_ref(v_x_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_636_){
_start:
{
lean_object* v_dir_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_dir_637_ = lean_ctor_get(v_self_636_, 4);
lean_inc_ref(v_dir_637_);
lean_dec_ref(v_self_636_);
v___x_638_ = l_Lake_defaultLakeDir;
v___x_639_ = l_Lake_joinRelative(v_dir_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_640_){
_start:
{
lean_object* v_config_641_; lean_object* v_toWorkspaceConfig_642_; lean_object* v___x_643_; 
v_config_641_ = lean_ctor_get(v_self_640_, 6);
lean_inc_ref(v_config_641_);
lean_dec_ref(v_self_640_);
v_toWorkspaceConfig_642_ = lean_ctor_get(v_config_641_, 0);
lean_inc_ref(v_toWorkspaceConfig_642_);
lean_dec_ref(v_config_641_);
v___x_643_ = l_System_FilePath_normalize(v_toWorkspaceConfig_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_644_){
_start:
{
lean_object* v_config_645_; lean_object* v_dir_646_; lean_object* v_toWorkspaceConfig_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_config_645_ = lean_ctor_get(v_self_644_, 6);
lean_inc_ref(v_config_645_);
v_dir_646_ = lean_ctor_get(v_self_644_, 4);
lean_inc_ref(v_dir_646_);
lean_dec_ref(v_self_644_);
v_toWorkspaceConfig_647_ = lean_ctor_get(v_config_645_, 0);
lean_inc_ref(v_toWorkspaceConfig_647_);
lean_dec_ref(v_config_645_);
v___x_648_ = l_System_FilePath_normalize(v_toWorkspaceConfig_647_);
v___x_649_ = l_Lake_joinRelative(v_dir_646_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_650_){
_start:
{
lean_object* v_dir_651_; lean_object* v_relManifestFile_652_; lean_object* v___x_653_; 
v_dir_651_ = lean_ctor_get(v_self_650_, 4);
lean_inc_ref(v_dir_651_);
v_relManifestFile_652_ = lean_ctor_get(v_self_650_, 9);
lean_inc_ref(v_relManifestFile_652_);
lean_dec_ref(v_self_650_);
v___x_653_ = l_Lake_joinRelative(v_dir_651_, v_relManifestFile_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_654_){
_start:
{
lean_object* v_config_655_; lean_object* v_dir_656_; lean_object* v_buildDir_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_config_655_ = lean_ctor_get(v_self_654_, 6);
lean_inc_ref(v_config_655_);
v_dir_656_ = lean_ctor_get(v_self_654_, 4);
lean_inc_ref(v_dir_656_);
lean_dec_ref(v_self_654_);
v_buildDir_657_ = lean_ctor_get(v_config_655_, 5);
lean_inc_ref(v_buildDir_657_);
lean_dec_ref(v_config_655_);
v___x_658_ = l_System_FilePath_normalize(v_buildDir_657_);
v___x_659_ = l_Lake_joinRelative(v_dir_656_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_660_){
_start:
{
lean_object* v_config_661_; lean_object* v_testDriverArgs_662_; 
v_config_661_ = lean_ctor_get(v_self_660_, 6);
v_testDriverArgs_662_ = lean_ctor_get(v_config_661_, 13);
lean_inc_ref(v_testDriverArgs_662_);
return v_testDriverArgs_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_Package_testDriverArgs(v_self_663_);
lean_dec_ref(v_self_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_665_){
_start:
{
lean_object* v_config_666_; lean_object* v_lintDriverArgs_667_; 
v_config_666_ = lean_ctor_get(v_self_665_, 6);
v_lintDriverArgs_667_ = lean_ctor_get(v_config_666_, 15);
lean_inc_ref(v_lintDriverArgs_667_);
return v_lintDriverArgs_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lake_Package_lintDriverArgs(v_self_668_);
lean_dec_ref(v_self_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_670_){
_start:
{
lean_object* v_config_671_; lean_object* v_extraDepTargets_672_; 
v_config_671_ = lean_ctor_get(v_self_670_, 6);
v_extraDepTargets_672_ = lean_ctor_get(v_config_671_, 2);
lean_inc_ref(v_extraDepTargets_672_);
return v_extraDepTargets_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lake_Package_extraDepTargets(v_self_673_);
lean_dec_ref(v_self_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_675_){
_start:
{
lean_object* v_config_676_; lean_object* v_toLeanConfig_677_; lean_object* v_platformIndependent_678_; 
v_config_676_ = lean_ctor_get(v_self_675_, 6);
v_toLeanConfig_677_ = lean_ctor_get(v_config_676_, 1);
v_platformIndependent_678_ = lean_ctor_get(v_toLeanConfig_677_, 10);
lean_inc(v_platformIndependent_678_);
return v_platformIndependent_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lake_Package_platformIndependent(v_self_679_);
lean_dec_ref(v_self_679_);
return v_res_680_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_687_){
_start:
{
lean_object* v_config_688_; lean_object* v_toLeanConfig_689_; lean_object* v_platformIndependent_690_; lean_object* v___f_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_config_688_ = lean_ctor_get(v_self_687_, 6);
lean_inc_ref(v_config_688_);
lean_dec_ref(v_self_687_);
v_toLeanConfig_689_ = lean_ctor_get(v_config_688_, 1);
lean_inc_ref(v_toLeanConfig_689_);
lean_dec_ref(v_config_688_);
v_platformIndependent_690_ = lean_ctor_get(v_toLeanConfig_689_, 10);
lean_inc(v_platformIndependent_690_);
lean_dec_ref(v_toLeanConfig_689_);
v___f_691_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_692_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__2));
v___x_693_ = l_Option_instBEq_beq___redArg(v___f_691_, v_platformIndependent_690_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lake_Package_isPlatformIndependent(v_self_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_697_){
_start:
{
lean_object* v_config_698_; uint8_t v_fixedToolchain_699_; 
v_config_698_ = lean_ctor_get(v_self_697_, 6);
v_fixedToolchain_699_ = lean_ctor_get_uint8(v_config_698_, sizeof(void*)*28 + 6);
return v_fixedToolchain_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lake_Package_fixedToolchain(v_self_700_);
lean_dec_ref(v_self_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_703_){
_start:
{
lean_object* v_config_704_; lean_object* v_releaseRepo_705_; 
v_config_704_ = lean_ctor_get(v_self_703_, 6);
v_releaseRepo_705_ = lean_ctor_get(v_config_704_, 10);
lean_inc(v_releaseRepo_705_);
return v_releaseRepo_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lake_Package_releaseRepo_x3f(v_self_706_);
lean_dec_ref(v_self_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_708_){
_start:
{
lean_object* v_remoteUrl_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_remoteUrl_709_ = lean_ctor_get(v_self_708_, 11);
v___x_710_ = lean_string_utf8_byte_size(v_remoteUrl_709_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_dec_eq(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_inc_ref(v_remoteUrl_709_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_remoteUrl_709_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lake_Package_remoteUrl_x3f(v_self_715_);
lean_dec_ref(v_self_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_717_){
_start:
{
lean_object* v_dir_718_; lean_object* v_buildArchive_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_dir_718_ = lean_ctor_get(v_self_717_, 4);
lean_inc_ref(v_dir_718_);
v_buildArchive_719_ = lean_ctor_get(v_self_717_, 21);
lean_inc_ref(v_buildArchive_719_);
lean_dec_ref(v_self_717_);
v___x_720_ = l_Lake_defaultLakeDir;
v___x_721_ = l_Lake_joinRelative(v_dir_718_, v___x_720_);
v___x_722_ = l_Lake_joinRelative(v___x_721_, v_buildArchive_719_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_724_){
_start:
{
lean_object* v_dir_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_dir_725_ = lean_ctor_get(v_self_724_, 4);
lean_inc_ref(v_dir_725_);
lean_dec_ref(v_self_724_);
v___x_726_ = l_Lake_defaultLakeDir;
v___x_727_ = l_Lake_joinRelative(v_dir_725_, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_729_ = l_Lake_joinRelative(v___x_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_730_){
_start:
{
lean_object* v_config_731_; uint8_t v_preferReleaseBuild_732_; 
v_config_731_ = lean_ctor_get(v_self_730_, 6);
v_preferReleaseBuild_732_ = lean_ctor_get_uint8(v_config_731_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Lake_Package_preferReleaseBuild(v_self_733_);
lean_dec_ref(v_self_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_736_){
_start:
{
lean_object* v_config_737_; uint8_t v_precompileModules_738_; 
v_config_737_ = lean_ctor_get(v_self_736_, 6);
v_precompileModules_738_ = lean_ctor_get_uint8(v_config_737_, sizeof(void*)*28 + 1);
return v_precompileModules_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Lake_Package_precompileModules(v_self_739_);
lean_dec_ref(v_self_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileImports(lean_object* v_self_742_){
_start:
{
lean_object* v_config_743_; lean_object* v_toLeanConfig_744_; uint8_t v_precompileImports_745_; 
v_config_743_ = lean_ctor_get(v_self_742_, 6);
v_toLeanConfig_744_ = lean_ctor_get(v_config_743_, 1);
v_precompileImports_745_ = lean_ctor_get_uint8(v_toLeanConfig_744_, sizeof(void*)*13 + 2);
return v_precompileImports_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileImports___boxed(lean_object* v_self_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lake_Package_precompileImports(v_self_746_);
lean_dec_ref(v_self_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_749_){
_start:
{
lean_object* v_config_750_; lean_object* v_moreGlobalServerArgs_751_; 
v_config_750_ = lean_ctor_get(v_self_749_, 6);
v_moreGlobalServerArgs_751_ = lean_ctor_get(v_config_750_, 3);
lean_inc_ref(v_moreGlobalServerArgs_751_);
return v_moreGlobalServerArgs_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lake_Package_moreGlobalServerArgs(v_self_752_);
lean_dec_ref(v_self_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_754_){
_start:
{
lean_object* v_config_755_; lean_object* v_toLeanConfig_756_; lean_object* v_leanOptions_757_; lean_object* v_moreServerOptions_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_config_755_ = lean_ctor_get(v_self_754_, 6);
v_toLeanConfig_756_ = lean_ctor_get(v_config_755_, 1);
v_leanOptions_757_ = lean_ctor_get(v_toLeanConfig_756_, 0);
v_moreServerOptions_758_ = lean_ctor_get(v_toLeanConfig_756_, 4);
v___x_759_ = l_Lean_LeanOptions_ofArray(v_leanOptions_757_);
v___x_760_ = l_Lean_LeanOptions_appendArray(v___x_759_, v_moreServerOptions_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_Package_moreServerOptions(v_self_761_);
lean_dec_ref(v_self_761_);
return v_res_762_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_763_){
_start:
{
lean_object* v_config_764_; lean_object* v_toLeanConfig_765_; uint8_t v_buildType_766_; 
v_config_764_ = lean_ctor_get(v_self_763_, 6);
v_toLeanConfig_765_ = lean_ctor_get(v_config_764_, 1);
v_buildType_766_ = lean_ctor_get_uint8(v_toLeanConfig_765_, sizeof(void*)*13);
return v_buildType_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lake_Package_buildType(v_self_767_);
lean_dec_ref(v_self_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_770_){
_start:
{
lean_object* v_config_771_; lean_object* v_toLeanConfig_772_; uint8_t v_backend_773_; 
v_config_771_ = lean_ctor_get(v_self_770_, 6);
v_toLeanConfig_772_ = lean_ctor_get(v_config_771_, 1);
v_backend_773_ = lean_ctor_get_uint8(v_toLeanConfig_772_, sizeof(void*)*13 + 1);
return v_backend_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lake_Package_backend(v_self_774_);
lean_dec_ref(v_self_774_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_777_){
_start:
{
lean_object* v_config_778_; uint8_t v_allowImportAll_779_; 
v_config_778_ = lean_ctor_get(v_self_777_, 6);
v_allowImportAll_779_ = lean_ctor_get_uint8(v_config_778_, sizeof(void*)*28 + 5);
return v_allowImportAll_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Lake_Package_allowImportAll(v_self_780_);
lean_dec_ref(v_self_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_requiresModuleSystem(lean_object* v_self_783_){
_start:
{
lean_object* v_config_784_; lean_object* v_toLeanConfig_785_; uint8_t v_requiresModuleSystem_786_; 
v_config_784_ = lean_ctor_get(v_self_783_, 6);
v_toLeanConfig_785_ = lean_ctor_get(v_config_784_, 1);
v_requiresModuleSystem_786_ = lean_ctor_get_uint8(v_toLeanConfig_785_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_requiresModuleSystem___boxed(lean_object* v_self_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Lake_Package_requiresModuleSystem(v_self_787_);
lean_dec_ref(v_self_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowNonModules(lean_object* v_self_790_){
_start:
{
lean_object* v_config_791_; lean_object* v_toLeanConfig_792_; uint8_t v_allowNonModules_793_; 
v_config_791_ = lean_ctor_get(v_self_790_, 6);
v_toLeanConfig_792_ = lean_ctor_get(v_config_791_, 1);
v_allowNonModules_793_ = lean_ctor_get_uint8(v_toLeanConfig_792_, sizeof(void*)*13 + 4);
return v_allowNonModules_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowNonModules___boxed(lean_object* v_self_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lake_Package_allowNonModules(v_self_794_);
lean_dec_ref(v_self_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_797_){
_start:
{
lean_object* v_config_798_; lean_object* v_toLeanConfig_799_; lean_object* v_dynlibs_800_; 
v_config_798_ = lean_ctor_get(v_self_797_, 6);
v_toLeanConfig_799_ = lean_ctor_get(v_config_798_, 1);
v_dynlibs_800_ = lean_ctor_get(v_toLeanConfig_799_, 11);
lean_inc_ref(v_dynlibs_800_);
return v_dynlibs_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lake_Package_dynlibs(v_self_801_);
lean_dec_ref(v_self_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_803_){
_start:
{
lean_object* v_config_804_; lean_object* v_toLeanConfig_805_; lean_object* v_plugins_806_; 
v_config_804_ = lean_ctor_get(v_self_803_, 6);
v_toLeanConfig_805_ = lean_ctor_get(v_config_804_, 1);
v_plugins_806_ = lean_ctor_get(v_toLeanConfig_805_, 12);
lean_inc_ref(v_plugins_806_);
return v_plugins_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lake_Package_plugins(v_self_807_);
lean_dec_ref(v_self_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_809_){
_start:
{
lean_object* v_config_810_; lean_object* v_toLeanConfig_811_; lean_object* v_leanOptions_812_; lean_object* v___x_813_; 
v_config_810_ = lean_ctor_get(v_self_809_, 6);
v_toLeanConfig_811_ = lean_ctor_get(v_config_810_, 1);
v_leanOptions_812_ = lean_ctor_get(v_toLeanConfig_811_, 0);
v___x_813_ = l_Lean_LeanOptions_ofArray(v_leanOptions_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lake_Package_leanOptions(v_self_814_);
lean_dec_ref(v_self_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_816_){
_start:
{
lean_object* v_config_817_; lean_object* v_toLeanConfig_818_; lean_object* v_moreLeanArgs_819_; 
v_config_817_ = lean_ctor_get(v_self_816_, 6);
v_toLeanConfig_818_ = lean_ctor_get(v_config_817_, 1);
v_moreLeanArgs_819_ = lean_ctor_get(v_toLeanConfig_818_, 1);
lean_inc_ref(v_moreLeanArgs_819_);
return v_moreLeanArgs_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lake_Package_moreLeanArgs(v_self_820_);
lean_dec_ref(v_self_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_822_){
_start:
{
lean_object* v_config_823_; lean_object* v_toLeanConfig_824_; lean_object* v_weakLeanArgs_825_; 
v_config_823_ = lean_ctor_get(v_self_822_, 6);
v_toLeanConfig_824_ = lean_ctor_get(v_config_823_, 1);
v_weakLeanArgs_825_ = lean_ctor_get(v_toLeanConfig_824_, 2);
lean_inc_ref(v_weakLeanArgs_825_);
return v_weakLeanArgs_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lake_Package_weakLeanArgs(v_self_826_);
lean_dec_ref(v_self_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_828_){
_start:
{
lean_object* v_config_829_; lean_object* v_toLeanConfig_830_; lean_object* v_moreLeancArgs_831_; 
v_config_829_ = lean_ctor_get(v_self_828_, 6);
v_toLeanConfig_830_ = lean_ctor_get(v_config_829_, 1);
v_moreLeancArgs_831_ = lean_ctor_get(v_toLeanConfig_830_, 3);
lean_inc_ref(v_moreLeancArgs_831_);
return v_moreLeancArgs_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_Package_moreLeancArgs(v_self_832_);
lean_dec_ref(v_self_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_834_){
_start:
{
lean_object* v_config_835_; lean_object* v_toLeanConfig_836_; lean_object* v_weakLeancArgs_837_; 
v_config_835_ = lean_ctor_get(v_self_834_, 6);
v_toLeanConfig_836_ = lean_ctor_get(v_config_835_, 1);
v_weakLeancArgs_837_ = lean_ctor_get(v_toLeanConfig_836_, 5);
lean_inc_ref(v_weakLeancArgs_837_);
return v_weakLeancArgs_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_Package_weakLeancArgs(v_self_838_);
lean_dec_ref(v_self_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_840_){
_start:
{
lean_object* v_config_841_; lean_object* v_toLeanConfig_842_; lean_object* v_moreLinkObjs_843_; 
v_config_841_ = lean_ctor_get(v_self_840_, 6);
v_toLeanConfig_842_ = lean_ctor_get(v_config_841_, 1);
v_moreLinkObjs_843_ = lean_ctor_get(v_toLeanConfig_842_, 6);
lean_inc_ref(v_moreLinkObjs_843_);
return v_moreLinkObjs_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lake_Package_moreLinkObjs(v_self_844_);
lean_dec_ref(v_self_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_846_){
_start:
{
lean_object* v_config_847_; lean_object* v_toLeanConfig_848_; lean_object* v_moreLinkLibs_849_; 
v_config_847_ = lean_ctor_get(v_self_846_, 6);
v_toLeanConfig_848_ = lean_ctor_get(v_config_847_, 1);
v_moreLinkLibs_849_ = lean_ctor_get(v_toLeanConfig_848_, 7);
lean_inc_ref(v_moreLinkLibs_849_);
return v_moreLinkLibs_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lake_Package_moreLinkLibs(v_self_850_);
lean_dec_ref(v_self_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_852_){
_start:
{
lean_object* v_config_853_; lean_object* v_toLeanConfig_854_; lean_object* v_moreLinkArgs_855_; 
v_config_853_ = lean_ctor_get(v_self_852_, 6);
v_toLeanConfig_854_ = lean_ctor_get(v_config_853_, 1);
v_moreLinkArgs_855_ = lean_ctor_get(v_toLeanConfig_854_, 8);
lean_inc_ref(v_moreLinkArgs_855_);
return v_moreLinkArgs_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lake_Package_moreLinkArgs(v_self_856_);
lean_dec_ref(v_self_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_858_){
_start:
{
lean_object* v_config_859_; lean_object* v_toLeanConfig_860_; lean_object* v_weakLinkArgs_861_; 
v_config_859_ = lean_ctor_get(v_self_858_, 6);
v_toLeanConfig_860_ = lean_ctor_get(v_config_859_, 1);
v_weakLinkArgs_861_ = lean_ctor_get(v_toLeanConfig_860_, 9);
lean_inc_ref(v_weakLinkArgs_861_);
return v_weakLinkArgs_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lake_Package_weakLinkArgs(v_self_862_);
lean_dec_ref(v_self_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_864_){
_start:
{
lean_object* v_config_865_; lean_object* v_dir_866_; lean_object* v_srcDir_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_config_865_ = lean_ctor_get(v_self_864_, 6);
lean_inc_ref(v_config_865_);
v_dir_866_ = lean_ctor_get(v_self_864_, 4);
lean_inc_ref(v_dir_866_);
lean_dec_ref(v_self_864_);
v_srcDir_867_ = lean_ctor_get(v_config_865_, 4);
lean_inc_ref(v_srcDir_867_);
lean_dec_ref(v_config_865_);
v___x_868_ = l_System_FilePath_normalize(v_srcDir_867_);
v___x_869_ = l_Lake_joinRelative(v_dir_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_870_){
_start:
{
lean_object* v_config_871_; lean_object* v_dir_872_; lean_object* v_srcDir_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_config_871_ = lean_ctor_get(v_self_870_, 6);
lean_inc_ref(v_config_871_);
v_dir_872_ = lean_ctor_get(v_self_870_, 4);
lean_inc_ref(v_dir_872_);
lean_dec_ref(v_self_870_);
v_srcDir_873_ = lean_ctor_get(v_config_871_, 4);
lean_inc_ref(v_srcDir_873_);
lean_dec_ref(v_config_871_);
v___x_874_ = l_System_FilePath_normalize(v_srcDir_873_);
v___x_875_ = l_Lake_joinRelative(v_dir_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_876_){
_start:
{
lean_object* v_config_877_; lean_object* v_dir_878_; lean_object* v_buildDir_879_; lean_object* v_leanLibDir_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_config_877_ = lean_ctor_get(v_self_876_, 6);
lean_inc_ref(v_config_877_);
v_dir_878_ = lean_ctor_get(v_self_876_, 4);
lean_inc_ref(v_dir_878_);
lean_dec_ref(v_self_876_);
v_buildDir_879_ = lean_ctor_get(v_config_877_, 5);
lean_inc_ref(v_buildDir_879_);
v_leanLibDir_880_ = lean_ctor_get(v_config_877_, 6);
lean_inc_ref(v_leanLibDir_880_);
lean_dec_ref(v_config_877_);
v___x_881_ = l_System_FilePath_normalize(v_buildDir_879_);
v___x_882_ = l_Lake_joinRelative(v_dir_878_, v___x_881_);
v___x_883_ = l_System_FilePath_normalize(v_leanLibDir_880_);
v___x_884_ = l_Lake_joinRelative(v___x_882_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrapIncludeDir(lean_object* v_self_886_){
_start:
{
lean_object* v_config_887_; lean_object* v_dir_888_; lean_object* v_buildDir_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_config_887_ = lean_ctor_get(v_self_886_, 6);
lean_inc_ref(v_config_887_);
v_dir_888_ = lean_ctor_get(v_self_886_, 4);
lean_inc_ref(v_dir_888_);
lean_dec_ref(v_self_886_);
v_buildDir_889_ = lean_ctor_get(v_config_887_, 5);
lean_inc_ref(v_buildDir_889_);
lean_dec_ref(v_config_887_);
v___x_890_ = l_System_FilePath_normalize(v_buildDir_889_);
v___x_891_ = l_Lake_joinRelative(v_dir_888_, v___x_890_);
v___x_892_ = ((lean_object*)(l_Lake_Package_bootstrapIncludeDir___closed__0));
v___x_893_ = l_Lake_joinRelative(v___x_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_894_){
_start:
{
lean_object* v_config_895_; lean_object* v_dir_896_; lean_object* v_buildDir_897_; lean_object* v_nativeLibDir_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_config_895_ = lean_ctor_get(v_self_894_, 6);
lean_inc_ref(v_config_895_);
v_dir_896_ = lean_ctor_get(v_self_894_, 4);
lean_inc_ref(v_dir_896_);
lean_dec_ref(v_self_894_);
v_buildDir_897_ = lean_ctor_get(v_config_895_, 5);
lean_inc_ref(v_buildDir_897_);
v_nativeLibDir_898_ = lean_ctor_get(v_config_895_, 7);
lean_inc_ref(v_nativeLibDir_898_);
lean_dec_ref(v_config_895_);
v___x_899_ = l_System_FilePath_normalize(v_buildDir_897_);
v___x_900_ = l_Lake_joinRelative(v_dir_896_, v___x_899_);
v___x_901_ = l_System_FilePath_normalize(v_nativeLibDir_898_);
v___x_902_ = l_Lake_joinRelative(v___x_900_, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_903_){
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
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_912_){
_start:
{
lean_object* v_config_913_; lean_object* v_dir_914_; lean_object* v_buildDir_915_; lean_object* v_binDir_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_config_913_ = lean_ctor_get(v_self_912_, 6);
lean_inc_ref(v_config_913_);
v_dir_914_ = lean_ctor_get(v_self_912_, 4);
lean_inc_ref(v_dir_914_);
lean_dec_ref(v_self_912_);
v_buildDir_915_ = lean_ctor_get(v_config_913_, 5);
lean_inc_ref(v_buildDir_915_);
v_binDir_916_ = lean_ctor_get(v_config_913_, 8);
lean_inc_ref(v_binDir_916_);
lean_dec_ref(v_config_913_);
v___x_917_ = l_System_FilePath_normalize(v_buildDir_915_);
v___x_918_ = l_Lake_joinRelative(v_dir_914_, v___x_917_);
v___x_919_ = l_System_FilePath_normalize(v_binDir_916_);
v___x_920_ = l_Lake_joinRelative(v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_921_){
_start:
{
lean_object* v_config_922_; lean_object* v_dir_923_; lean_object* v_buildDir_924_; lean_object* v_irDir_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_config_922_ = lean_ctor_get(v_self_921_, 6);
lean_inc_ref(v_config_922_);
v_dir_923_ = lean_ctor_get(v_self_921_, 4);
lean_inc_ref(v_dir_923_);
lean_dec_ref(v_self_921_);
v_buildDir_924_ = lean_ctor_get(v_config_922_, 5);
lean_inc_ref(v_buildDir_924_);
v_irDir_925_ = lean_ctor_get(v_config_922_, 9);
lean_inc_ref(v_irDir_925_);
lean_dec_ref(v_config_922_);
v___x_926_ = l_System_FilePath_normalize(v_buildDir_924_);
v___x_927_ = l_Lake_joinRelative(v_dir_923_, v___x_926_);
v___x_928_ = l_System_FilePath_normalize(v_irDir_925_);
v___x_929_ = l_Lake_joinRelative(v___x_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_930_){
_start:
{
lean_object* v_config_931_; uint8_t v_libPrefixOnWindows_932_; 
v_config_931_ = lean_ctor_get(v_self_930_, 6);
v_libPrefixOnWindows_932_ = lean_ctor_get_uint8(v_config_931_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Lake_Package_libPrefixOnWindows(v_self_933_);
lean_dec_ref(v_self_933_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_936_){
_start:
{
lean_object* v_config_937_; lean_object* v_enableArtifactCache_x3f_938_; 
v_config_937_ = lean_ctor_get(v_self_936_, 6);
v_enableArtifactCache_x3f_938_ = lean_ctor_get(v_config_937_, 24);
lean_inc(v_enableArtifactCache_x3f_938_);
return v_enableArtifactCache_x3f_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lake_Package_enableArtifactCache_x3f(v_self_939_);
lean_dec_ref(v_self_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_941_){
_start:
{
lean_object* v_config_942_; lean_object* v_restoreAllArtifacts_x3f_943_; 
v_config_942_ = lean_ctor_get(v_self_941_, 6);
v_restoreAllArtifacts_x3f_943_ = lean_ctor_get(v_config_942_, 25);
lean_inc(v_restoreAllArtifacts_x3f_943_);
return v_restoreAllArtifacts_x3f_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_944_);
lean_dec_ref(v_self_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_946_){
_start:
{
lean_object* v_baseName_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v_baseName_947_ = lean_ctor_get(v_self_946_, 1);
lean_inc(v_baseName_947_);
lean_dec_ref(v_self_946_);
v___x_948_ = 0;
v___x_949_ = l_Lean_Name_toString(v_baseName_947_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_951_){
_start:
{
lean_object* v_origName_952_; lean_object* v_scope_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_origName_952_ = lean_ctor_get(v_self_951_, 3);
lean_inc(v_origName_952_);
v_scope_953_ = lean_ctor_get(v_self_951_, 10);
lean_inc_ref(v_scope_953_);
lean_dec_ref(v_self_951_);
v___x_954_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_955_ = lean_string_append(v_scope_953_, v___x_954_);
v___x_956_ = 0;
v___x_957_ = l_Lean_Name_toString(v_origName_952_, v___x_956_);
v___x_958_ = lean_string_append(v___x_955_, v___x_957_);
lean_dec_ref(v___x_957_);
v___x_959_ = l_Lake_CacheServiceScope_ofString(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_960_){
_start:
{
lean_object* v_scope_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_scope_961_ = lean_ctor_get(v_self_960_, 10);
v___x_962_ = lean_string_utf8_byte_size(v_scope_961_);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_nat_dec_eq(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_960_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; 
lean_dec_ref(v_self_960_);
v___x_967_ = lean_box(0);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_968_, lean_object* v_k_969_){
_start:
{
if (lean_obj_tag(v_t_968_) == 0)
{
lean_object* v_k_970_; lean_object* v_v_971_; lean_object* v_l_972_; lean_object* v_r_973_; uint8_t v___x_974_; 
v_k_970_ = lean_ctor_get(v_t_968_, 1);
v_v_971_ = lean_ctor_get(v_t_968_, 2);
v_l_972_ = lean_ctor_get(v_t_968_, 3);
v_r_973_ = lean_ctor_get(v_t_968_, 4);
v___x_974_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_969_, v_k_970_);
switch(v___x_974_)
{
case 0:
{
v_t_968_ = v_l_972_;
goto _start;
}
case 1:
{
lean_object* v___x_976_; 
lean_inc(v_v_971_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_v_971_);
return v___x_976_;
}
default: 
{
v_t_968_ = v_r_973_;
goto _start;
}
}
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_979_, lean_object* v_k_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_979_, v_k_980_);
lean_dec(v_k_980_);
lean_dec(v_t_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_982_, lean_object* v_self_983_){
_start:
{
lean_object* v_targetDeclMap_984_; lean_object* v___x_985_; 
v_targetDeclMap_984_ = lean_ctor_get(v_self_983_, 16);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_984_, v_name_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_986_, lean_object* v_self_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lake_Package_findTargetDecl_x3f(v_name_986_, v_self_987_);
lean_dec_ref(v_self_987_);
lean_dec(v_name_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_989_, lean_object* v_inst_990_, lean_object* v_t_991_, lean_object* v_k_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_991_, v_k_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_994_, lean_object* v_inst_995_, lean_object* v_t_996_, lean_object* v_k_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_994_, v_inst_995_, v_t_996_, v_k_997_);
lean_dec(v_k_997_);
lean_dec(v_t_996_);
return v_res_998_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_1002_, lean_object* v_as_1003_, size_t v_i_1004_, size_t v_stop_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_1004_, v_stop_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v_kind_1008_; lean_object* v_config_1009_; uint8_t v___x_1010_; uint8_t v___y_1012_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_1003_, v_i_1004_);
v_kind_1008_ = lean_ctor_get(v___x_1007_, 2);
v_config_1009_ = lean_ctor_get(v___x_1007_, 3);
v___x_1010_ = 1;
v___x_1016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1017_ = lean_name_eq(v_kind_1008_, v___x_1016_);
if (v___x_1017_ == 0)
{
v___y_1012_ = v___x_1017_;
goto v___jp_1011_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_1002_, v_config_1009_);
v___y_1012_ = v___x_1018_;
goto v___jp_1011_;
}
v___jp_1011_:
{
if (v___y_1012_ == 0)
{
size_t v___x_1013_; size_t v___x_1014_; 
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_add(v_i_1004_, v___x_1013_);
v_i_1004_ = v___x_1014_;
goto _start;
}
else
{
return v___x_1010_;
}
}
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = 0;
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_1020_, lean_object* v_as_1021_, lean_object* v_i_1022_, lean_object* v_stop_1023_){
_start:
{
size_t v_i_boxed_1024_; size_t v_stop_boxed_1025_; uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_i_boxed_1024_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_stop_boxed_1025_ = lean_unbox_usize(v_stop_1023_);
lean_dec(v_stop_1023_);
v_res_1026_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1020_, v_as_1021_, v_i_boxed_1024_, v_stop_boxed_1025_);
lean_dec_ref(v_as_1021_);
lean_dec(v_mod_1020_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_1028_, lean_object* v_self_1029_){
_start:
{
lean_object* v_targetDecls_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_targetDecls_1030_ = lean_ctor_get(v_self_1029_, 15);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v_targetDecls_1030_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
return v___x_1033_;
}
else
{
if (v___x_1033_ == 0)
{
return v___x_1033_;
}
else
{
size_t v___x_1034_; size_t v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = lean_usize_of_nat(v___x_1032_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_1028_, v_targetDecls_1030_, v___x_1034_, v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_1037_, lean_object* v_self_1038_){
_start:
{
uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_res_1039_ = l_Lake_Package_isLocalModule(v_mod_1037_, v_self_1038_);
lean_dec_ref(v_self_1038_);
lean_dec(v_mod_1037_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_1041_, lean_object* v_as_1042_, size_t v_i_1043_, size_t v_stop_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_eq(v_i_1043_, v_stop_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v_kind_1047_; lean_object* v_config_1048_; uint8_t v___x_1049_; uint8_t v___y_1051_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1046_ = lean_array_uget_borrowed(v_as_1042_, v_i_1043_);
v_kind_1047_ = lean_ctor_get(v___x_1046_, 2);
v_config_1048_ = lean_ctor_get(v___x_1046_, 3);
v___x_1049_ = 1;
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_1063_ = lean_name_eq(v_kind_1047_, v___x_1062_);
if (v___x_1063_ == 0)
{
goto v___jp_1055_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1041_, v_config_1048_);
if (v___x_1064_ == 0)
{
goto v___jp_1055_;
}
else
{
v___y_1051_ = v___x_1064_;
goto v___jp_1050_;
}
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
size_t v___x_1052_; size_t v___x_1053_; 
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1043_, v___x_1052_);
v_i_1043_ = v___x_1053_;
goto _start;
}
else
{
return v___x_1049_;
}
}
v___jp_1055_:
{
lean_object* v_kind_1056_; lean_object* v_config_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_kind_1056_ = lean_ctor_get(v___x_1046_, 2);
v_config_1057_ = lean_ctor_get(v___x_1046_, 3);
v___x_1058_ = l_Lake_LeanExe_keyword;
v___x_1059_ = lean_name_eq(v_kind_1056_, v___x_1058_);
if (v___x_1059_ == 0)
{
v___y_1051_ = v___x_1059_;
goto v___jp_1050_;
}
else
{
lean_object* v_root_1060_; uint8_t v___x_1061_; 
v_root_1060_ = lean_ctor_get(v_config_1057_, 2);
v___x_1061_ = lean_name_eq(v_root_1060_, v_mod_1041_);
v___y_1051_ = v___x_1061_;
goto v___jp_1050_;
}
}
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = 0;
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_1066_, lean_object* v_as_1067_, lean_object* v_i_1068_, lean_object* v_stop_1069_){
_start:
{
size_t v_i_boxed_1070_; size_t v_stop_boxed_1071_; uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_i_boxed_1070_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_stop_boxed_1071_ = lean_unbox_usize(v_stop_1069_);
lean_dec(v_stop_1069_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1066_, v_as_1067_, v_i_boxed_1070_, v_stop_boxed_1071_);
lean_dec_ref(v_as_1067_);
lean_dec(v_mod_1066_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_1074_, lean_object* v_self_1075_){
_start:
{
lean_object* v_targetDecls_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_targetDecls_1076_ = lean_ctor_get(v_self_1075_, 15);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_array_get_size(v_targetDecls_1076_);
v___x_1079_ = lean_nat_dec_lt(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
return v___x_1079_;
}
else
{
if (v___x_1079_ == 0)
{
return v___x_1079_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = lean_usize_of_nat(v___x_1078_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_1074_, v_targetDecls_1076_, v___x_1080_, v___x_1081_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_1083_, lean_object* v_self_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Lake_Package_isBuildableModule(v_mod_1083_, v_self_1084_);
lean_dec_ref(v_self_1084_);
lean_dec(v_mod_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_1087_){
_start:
{
lean_object* v_config_1089_; lean_object* v_dir_1090_; lean_object* v_buildDir_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_config_1089_ = lean_ctor_get(v_self_1087_, 6);
lean_inc_ref(v_config_1089_);
v_dir_1090_ = lean_ctor_get(v_self_1087_, 4);
lean_inc_ref(v_dir_1090_);
lean_dec_ref(v_self_1087_);
v_buildDir_1091_ = lean_ctor_get(v_config_1089_, 5);
lean_inc_ref(v_buildDir_1091_);
lean_dec_ref(v_config_1089_);
v___x_1092_ = l_System_FilePath_normalize(v_buildDir_1091_);
v___x_1093_ = l_Lake_joinRelative(v_dir_1090_, v___x_1092_);
v___x_1094_ = l_Lake_removeDirAllIfExists(v___x_1093_);
lean_dec_ref(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lake_Package_clean(v_self_1095_);
return v_res_1097_;
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
