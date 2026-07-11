// Lean compiler output
// Module: Lake.Config.Env
// Imports: public import Lake.Config.Cache public import Lake.Config.InstallPath import Init.System.Platform
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lake_envToBool_x3f(lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
extern lean_object* l_Lean_toolchain;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedLeanInstall_default;
extern lean_object* l_Lake_instInhabitedLakeInstall_default;
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedEnv_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedEnv_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedEnv_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedEnv_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
static const lean_string_object l_Lake_getUserHome_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HOME"};
static const lean_object* l_Lake_getUserHome_x3f___closed__0 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__0_value;
static const lean_string_object l_Lake_getUserHome_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "HOMEDRIVE"};
static const lean_object* l_Lake_getUserHome_x3f___closed__1 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__1_value;
static const lean_string_object l_Lake_getUserHome_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HOMEPATH"};
static const lean_object* l_Lake_getUserHome_x3f___closed__2 = (const lean_object*)&l_Lake_getUserHome_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "XDG_CACHE_HOME"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f();
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Env_computeToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ELAN_TOOLCHAIN"};
static const lean_object* l_Lake_Env_computeToolchain___closed__0 = (const lean_object*)&l_Lake_Env_computeToolchain___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain();
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_DIR"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LAKE_PKG_URL_MAP"};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value;
static const lean_string_object l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "'LAKE_PKG_URL_MAP' has invalid JSON: "};
static const lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1 = (const lean_object*)&l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object*);
static const lean_string_object l_Lake_Env_compute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lake"};
static const lean_object* l_Lake_Env_compute___closed__0 = (const lean_object*)&l_Lake_Env_compute___closed__0_value;
static const lean_string_object l_Lake_Env_compute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config.toml"};
static const lean_object* l_Lake_Env_compute___closed__1 = (const lean_object*)&l_Lake_Env_compute___closed__1_value;
static const lean_string_object l_Lake_Env_compute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LAKE_NO_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__2 = (const lean_object*)&l_Lake_Env_compute___closed__2_value;
static const lean_string_object l_Lake_Env_compute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_ARTIFACT_CACHE"};
static const lean_object* l_Lake_Env_compute___closed__3 = (const lean_object*)&l_Lake_Env_compute___closed__3_value;
static const lean_string_object l_Lake_Env_compute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LAKE_RESTORE_ARTIFACTS"};
static const lean_object* l_Lake_Env_compute___closed__4 = (const lean_object*)&l_Lake_Env_compute___closed__4_value;
static const lean_string_object l_Lake_Env_compute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LAKE_CONFIG"};
static const lean_object* l_Lake_Env_compute___closed__5 = (const lean_object*)&l_Lake_Env_compute___closed__5_value;
static const lean_string_object l_Lake_Env_compute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_KEY"};
static const lean_object* l_Lake_Env_compute___closed__6 = (const lean_object*)&l_Lake_Env_compute___closed__6_value;
static const lean_string_object l_Lake_Env_compute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_ARTIFACT_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__7 = (const lean_object*)&l_Lake_Env_compute___closed__7_value;
static const lean_string_object l_Lake_Env_compute___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "LAKE_CACHE_REVISION_ENDPOINT"};
static const lean_object* l_Lake_Env_compute___closed__8 = (const lean_object*)&l_Lake_Env_compute___closed__8_value;
static const lean_string_object l_Lake_Env_compute___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_CACHE_SERVICE"};
static const lean_object* l_Lake_Env_compute___closed__9 = (const lean_object*)&l_Lake_Env_compute___closed__9_value;
static const lean_string_object l_Lake_Env_compute___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_GITHASH"};
static const lean_object* l_Lake_Env_compute___closed__10 = (const lean_object*)&l_Lake_Env_compute___closed__10_value;
static const lean_string_object l_Lake_Env_compute___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_Env_compute___closed__11 = (const lean_object*)&l_Lake_Env_compute___closed__11_value;
static const lean_string_object l_Lake_Env_compute___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lake_Env_compute___closed__12 = (const lean_object*)&l_Lake_Env_compute___closed__12_value;
static const lean_string_object l_Lake_Env_compute___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_Env_compute___closed__13 = (const lean_object*)&l_Lake_Env_compute___closed__13_value;
static const lean_string_object l_Lake_Env_compute___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "RESERVOIR_API_BASE_URL"};
static const lean_object* l_Lake_Env_compute___closed__14 = (const lean_object*)&l_Lake_Env_compute___closed__14_value;
static const lean_string_object l_Lake_Env_compute___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "RESERVOIR_API_URL"};
static const lean_object* l_Lake_Env_compute___closed__15 = (const lean_object*)&l_Lake_Env_compute___closed__15_value;
static const lean_string_object l_Lake_Env_compute___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/v1"};
static const lean_object* l_Lake_Env_compute___closed__16 = (const lean_object*)&l_Lake_Env_compute___closed__16_value;
static const lean_string_object l_Lake_Env_compute___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "https://reservoir.lean-lang.org/api"};
static const lean_object* l_Lake_Env_compute___closed__17 = (const lean_object*)&l_Lake_Env_compute___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_computeToolchain___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__0 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__0_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LAKE"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__1 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__1_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__2 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__2_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_OVERRIDE_LEAN"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__3 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__3_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__4 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__4_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LAKE_HOME"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__5 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__5_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__6 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__6_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LEAN"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__7 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__7_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__8 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__8_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_compute___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__9 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__9_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__10 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__10_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__11 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__11_value;
static const lean_string_object l_Lake_Env_noToolchainVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_AR"};
static const lean_object* l_Lake_Env_noToolchainVars___closed__12 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__12_value;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Env_noToolchainVars___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__13 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__13_value;
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__14;
static lean_once_cell_t l_Lake_Env_noToolchainVars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Env_noToolchainVars___closed__15;
static const lean_ctor_object l_Lake_Env_noToolchainVars___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instInhabitedEnv_default___closed__0_value)}};
static const lean_object* l_Lake_Env_noToolchainVars___closed__16 = (const lean_object*)&l_Lake_Env_noToolchainVars___closed__16_value;
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object*);
static const lean_string_object l_Lake_Env_baseVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_CC"};
static const lean_object* l_Lake_Env_baseVars___closed__0 = (const lean_object*)&l_Lake_Env_baseVars___closed__0_value;
static const lean_string_object l_Lake_Env_baseVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Env_baseVars___closed__1 = (const lean_object*)&l_Lake_Env_baseVars___closed__1_value;
static const lean_string_object l_Lake_Env_baseVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Env_baseVars___closed__2 = (const lean_object*)&l_Lake_Env_baseVars___closed__2_value;
static const lean_string_object l_Lake_Env_baseVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_Env_baseVars___closed__3 = (const lean_object*)&l_Lake_Env_baseVars___closed__3_value;
static const lean_string_object l_Lake_Env_baseVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_Env_baseVars___closed__4 = (const lean_object*)&l_Lake_Env_baseVars___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0___boxed(lean_object*);
static const lean_ctor_object l_Lake_Env_vars___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__1_value)}};
static const lean_object* l_Lake_Env_vars___lam__1___closed__0 = (const lean_object*)&l_Lake_Env_vars___lam__1___closed__0_value;
static const lean_ctor_object l_Lake_Env_vars___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Env_baseVars___closed__2_value)}};
static const lean_object* l_Lake_Env_vars___lam__1___closed__1 = (const lean_object*)&l_Lake_Env_vars___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv_default___closed__1(void){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_2_ = lean_box(0);
v___x_3_ = 0;
v___x_4_ = lean_box(1);
v___x_5_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = l_Lake_instInhabitedLeanInstall_default;
v___x_8_ = l_Lake_instInhabitedLakeInstall_default;
v___x_9_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_6_);
lean_ctor_set(v___x_9_, 3, v___x_5_);
lean_ctor_set(v___x_9_, 4, v___x_5_);
lean_ctor_set(v___x_9_, 5, v___x_4_);
lean_ctor_set(v___x_9_, 6, v___x_6_);
lean_ctor_set(v___x_9_, 7, v___x_6_);
lean_ctor_set(v___x_9_, 8, v___x_6_);
lean_ctor_set(v___x_9_, 9, v___x_6_);
lean_ctor_set(v___x_9_, 10, v___x_6_);
lean_ctor_set(v___x_9_, 11, v___x_6_);
lean_ctor_set(v___x_9_, 12, v___x_6_);
lean_ctor_set(v___x_9_, 13, v___x_6_);
lean_ctor_set(v___x_9_, 14, v___x_6_);
lean_ctor_set(v___x_9_, 15, v___x_2_);
lean_ctor_set(v___x_9_, 16, v___x_2_);
lean_ctor_set(v___x_9_, 17, v___x_2_);
lean_ctor_set(v___x_9_, 18, v___x_2_);
lean_ctor_set(v___x_9_, 19, v___x_5_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*20, v___x_3_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*20 + 1, v___x_3_);
return v___x_9_;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv_default(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lake_instInhabitedEnv_default___closed__1, &l_Lake_instInhabitedEnv_default___closed__1_once, _init_l_Lake_instInhabitedEnv_default___closed__1);
return v___x_10_;
}
}
static lean_object* _init_l_Lake_instInhabitedEnv(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_instInhabitedEnv_default;
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f(){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_System_Platform_isWindows;
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__0));
v___x_18_ = lean_io_getenv(v___x_17_);
if (lean_obj_tag(v___x_18_) == 1)
{
lean_object* v_val_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
v_val_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_val_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_val_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v___x_27_; 
lean_dec(v___x_18_);
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__1));
v___x_29_ = lean_io_getenv(v___x_28_);
if (lean_obj_tag(v___x_29_) == 1)
{
lean_object* v_val_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_val_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_val_30_);
lean_dec_ref_known(v___x_29_, 1);
v___x_31_ = ((lean_object*)(l_Lake_getUserHome_x3f___closed__2));
v___x_32_ = lean_io_getenv(v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_41_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_41_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_string_append(v_val_30_, v_val_33_);
lean_dec(v_val_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v___x_42_; 
lean_dec(v___x_32_);
lean_dec(v_val_30_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v___x_29_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUserHome_x3f___boxed(lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_getUserHome_x3f();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(lean_object* v_userHome_x3f_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_51_ = lean_io_getenv(v___x_50_);
if (lean_obj_tag(v___x_51_) == 1)
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_userHome_x3f_48_);
v_val_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_val_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_dec(v___x_51_);
if (lean_obj_tag(v_userHome_x3f_48_) == 1)
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_69_; 
v_val_60_ = lean_ctor_get(v_userHome_x3f_48_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_userHome_x3f_48_);
if (v_isSharedCheck_69_ == 0)
{
v___x_62_ = v_userHome_x3f_48_;
v_isShared_63_ = v_isSharedCheck_69_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_userHome_x3f_48_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_69_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_65_ = l_System_FilePath_join(v_val_60_, v___x_64_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_65_);
v___x_67_ = v___x_62_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v___x_70_; 
lean_dec(v_userHome_x3f_48_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(lean_object* v_userHome_x3f_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f(){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0));
v___x_76_ = lean_io_getenv(v___x_75_);
if (lean_obj_tag(v___x_76_) == 1)
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_val_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_val_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v___x_85_; 
lean_dec(v___x_76_);
v___x_85_ = l_Lake_getUserHome_x3f();
if (lean_obj_tag(v___x_85_) == 1)
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_95_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1));
v___x_91_ = l_System_FilePath_join(v_val_86_, v___x_90_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v___x_85_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSystemCacheHome_x3f___boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_getSystemCacheHome_x3f();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(lean_object* v_elan_101_, lean_object* v_toolchain_102_){
_start:
{
lean_object* v_toolchainsDir_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_toolchainsDir_103_ = lean_ctor_get(v_elan_101_, 3);
lean_inc_ref(v_toolchainsDir_103_);
lean_dec_ref(v_elan_101_);
v___x_104_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_102_, v___x_104_, v___x_105_);
v___x_107_ = l_System_FilePath_join(v_toolchainsDir_103_, v___x_106_);
v___x_108_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_109_ = l_System_FilePath_join(v___x_107_, v___x_108_);
v___x_110_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1));
v___x_111_ = l_System_FilePath_join(v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(lean_object* v_elan_112_, lean_object* v_toolchain_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_112_, v_toolchain_113_);
lean_dec_ref(v_toolchain_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(lean_object* v_elan_115_, lean_object* v_toolchain_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_string_utf8_byte_size(v_toolchain_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_elan_115_, v_toolchain_116_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec_ref(v_elan_115_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(lean_object* v_elan_123_, lean_object* v_toolchain_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(v_elan_123_, v_toolchain_124_);
lean_dec_ref(v_toolchain_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_129_ = lean_io_getenv(v___x_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_toolchain;
return v___x_130_;
}
else
{
lean_object* v_val_131_; 
v_val_131_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v___x_129_, 1);
return v_val_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeToolchain___boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lake_Env_computeToolchain();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f(){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_137_ = lean_io_getenv(v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_150_; 
v_val_139_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_141_ = v___x_137_;
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_val_139_);
lean_dec(v___x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_150_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = lean_string_utf8_byte_size(v_val_139_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_del_object(v___x_141_);
lean_dec(v_val_139_);
v___x_146_ = lean_box(0);
return v___x_146_;
}
else
{
lean_object* v___x_148_; 
if (v_isShared_142_ == 0)
{
v___x_148_ = v___x_141_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_val_139_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(lean_object* v_cacheHome_x3f_153_){
_start:
{
if (lean_obj_tag(v_cacheHome_x3f_153_) == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
v_val_155_ = lean_ctor_get(v_cacheHome_x3f_153_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_cacheHome_x3f_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v_cacheHome_x3f_153_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v_cacheHome_x3f_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_160_ = l_System_FilePath_join(v_val_155_, v___x_159_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(lean_object* v_elan_x3f_165_, lean_object* v_toolchain_166_){
_start:
{
if (lean_obj_tag(v_elan_x3f_165_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_181_; 
v_val_168_ = lean_ctor_get(v_elan_x3f_165_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_elan_x3f_165_);
if (v_isSharedCheck_181_ == 0)
{
v___x_170_ = v_elan_x3f_165_;
v_isShared_171_ = v_isSharedCheck_181_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_val_168_);
lean_dec(v_elan_x3f_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_181_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_string_utf8_byte_size(v_toolchain_166_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
v___x_175_ = lean_bool_not(v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_del_object(v___x_170_);
lean_dec(v_val_168_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_168_, v_toolchain_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_177_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object* v_elan_x3f_182_, lean_object* v_toolchain_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(v_elan_x3f_182_, v_toolchain_183_);
lean_dec_ref(v_toolchain_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object* v_elan_x3f_185_, lean_object* v_toolchain_186_){
_start:
{
lean_object* v_cache_189_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_198_ = lean_io_getenv(v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
goto v___jp_199_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_val_206_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v___x_198_, 1);
v___x_207_ = lean_string_utf8_byte_size(v_val_206_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_val_206_);
goto v___jp_199_;
}
else
{
lean_dec(v_elan_x3f_185_);
v_cache_189_ = v_val_206_;
goto v___jp_188_;
}
}
v___jp_188_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_cache_189_);
return v___x_190_;
}
v___jp_191_:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_val_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_val_194_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_192_, 1);
v___x_195_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_196_ = l_System_FilePath_join(v_val_194_, v___x_195_);
v_cache_189_ = v___x_196_;
goto v___jp_188_;
}
}
v___jp_199_:
{
if (lean_obj_tag(v_elan_x3f_185_) == 0)
{
goto v___jp_191_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; uint8_t v___x_204_; 
v_val_200_ = lean_ctor_get(v_elan_x3f_185_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v_elan_x3f_185_, 1);
v___x_201_ = lean_string_utf8_byte_size(v_toolchain_186_);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_nat_dec_eq(v___x_201_, v___x_202_);
v___x_204_ = lean_bool_not(v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_val_200_);
goto v___jp_191_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_200_, v_toolchain_186_);
v_cache_189_ = v___x_205_;
goto v___jp_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* v_elan_x3f_210_, lean_object* v_toolchain_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_210_, v_toolchain_211_);
lean_dec_ref(v_toolchain_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* v_elan_x3f_214_, lean_object* v_userHome_x3f_215_, lean_object* v_toolchain_216_, lean_object* v_env_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_220_ = lean_io_getenv(v___x_219_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v_val_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_userHome_x3f_215_);
lean_dec(v_elan_x3f_214_);
v_val_264_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_333_ == 0)
{
v___x_266_ = v___x_220_;
v_isShared_267_ = v_isSharedCheck_333_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_val_264_);
lean_dec(v___x_220_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_333_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_string_utf8_byte_size(v_val_264_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_nat_dec_eq(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v_lake_271_; lean_object* v_lean_272_; lean_object* v_elan_x3f_273_; lean_object* v_reservoirApiUrl_274_; lean_object* v_githashOverride_275_; lean_object* v_pkgUrlMap_276_; uint8_t v_noCache_277_; lean_object* v_enableArtifactCache_x3f_278_; lean_object* v_restoreAllArtifacts_x3f_279_; uint8_t v_noSystemCache_280_; lean_object* v_lakeConfig_x3f_281_; lean_object* v_cacheKey_x3f_282_; lean_object* v_cacheArtifactEndpoint_x3f_283_; lean_object* v_cacheRevisionEndpoint_x3f_284_; lean_object* v_cacheService_x3f_285_; lean_object* v_initLeanPath_286_; lean_object* v_initLeanSrcPath_287_; lean_object* v_initSharedLibPath_288_; lean_object* v_initPath_289_; lean_object* v_toolchain_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
v_lake_271_ = lean_ctor_get(v_env_217_, 0);
v_lean_272_ = lean_ctor_get(v_env_217_, 1);
v_elan_x3f_273_ = lean_ctor_get(v_env_217_, 2);
v_reservoirApiUrl_274_ = lean_ctor_get(v_env_217_, 3);
v_githashOverride_275_ = lean_ctor_get(v_env_217_, 4);
v_pkgUrlMap_276_ = lean_ctor_get(v_env_217_, 5);
v_noCache_277_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20);
v_enableArtifactCache_x3f_278_ = lean_ctor_get(v_env_217_, 6);
v_restoreAllArtifacts_x3f_279_ = lean_ctor_get(v_env_217_, 7);
v_noSystemCache_280_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_281_ = lean_ctor_get(v_env_217_, 10);
v_cacheKey_x3f_282_ = lean_ctor_get(v_env_217_, 11);
v_cacheArtifactEndpoint_x3f_283_ = lean_ctor_get(v_env_217_, 12);
v_cacheRevisionEndpoint_x3f_284_ = lean_ctor_get(v_env_217_, 13);
v_cacheService_x3f_285_ = lean_ctor_get(v_env_217_, 14);
v_initLeanPath_286_ = lean_ctor_get(v_env_217_, 15);
v_initLeanSrcPath_287_ = lean_ctor_get(v_env_217_, 16);
v_initSharedLibPath_288_ = lean_ctor_get(v_env_217_, 17);
v_initPath_289_ = lean_ctor_get(v_env_217_, 18);
v_toolchain_290_ = lean_ctor_get(v_env_217_, 19);
v_isSharedCheck_301_ = !lean_is_exclusive(v_env_217_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_env_217_, 9);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_env_217_, 8);
lean_dec(v_unused_303_);
v___x_292_ = v_env_217_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_toolchain_290_);
lean_inc(v_initPath_289_);
lean_inc(v_initSharedLibPath_288_);
lean_inc(v_initLeanSrcPath_287_);
lean_inc(v_initLeanPath_286_);
lean_inc(v_cacheService_x3f_285_);
lean_inc(v_cacheRevisionEndpoint_x3f_284_);
lean_inc(v_cacheArtifactEndpoint_x3f_283_);
lean_inc(v_cacheKey_x3f_282_);
lean_inc(v_lakeConfig_x3f_281_);
lean_inc(v_restoreAllArtifacts_x3f_279_);
lean_inc(v_enableArtifactCache_x3f_278_);
lean_inc(v_pkgUrlMap_276_);
lean_inc(v_githashOverride_275_);
lean_inc(v_reservoirApiUrl_274_);
lean_inc(v_elan_x3f_273_);
lean_inc(v_lean_272_);
lean_inc(v_lake_271_);
lean_dec(v_env_217_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_267_ == 0)
{
v___x_295_ = v___x_266_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_val_264_);
v___x_295_ = v_reuseFailAlloc_300_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
lean_inc_ref(v___x_295_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 9, v___x_295_);
lean_ctor_set(v___x_292_, 8, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_lake_271_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_lean_272_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_elan_x3f_273_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_reservoirApiUrl_274_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_githashOverride_275_);
lean_ctor_set(v_reuseFailAlloc_299_, 5, v_pkgUrlMap_276_);
lean_ctor_set(v_reuseFailAlloc_299_, 6, v_enableArtifactCache_x3f_278_);
lean_ctor_set(v_reuseFailAlloc_299_, 7, v_restoreAllArtifacts_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_299_, 8, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 9, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 10, v_lakeConfig_x3f_281_);
lean_ctor_set(v_reuseFailAlloc_299_, 11, v_cacheKey_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_299_, 12, v_cacheArtifactEndpoint_x3f_283_);
lean_ctor_set(v_reuseFailAlloc_299_, 13, v_cacheRevisionEndpoint_x3f_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 14, v_cacheService_x3f_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 15, v_initLeanPath_286_);
lean_ctor_set(v_reuseFailAlloc_299_, 16, v_initLeanSrcPath_287_);
lean_ctor_set(v_reuseFailAlloc_299_, 17, v_initSharedLibPath_288_);
lean_ctor_set(v_reuseFailAlloc_299_, 18, v_initPath_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 19, v_toolchain_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_299_, sizeof(void*)*20, v_noCache_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_299_, sizeof(void*)*20 + 1, v_noSystemCache_280_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
}
}
else
{
lean_object* v_lake_304_; lean_object* v_lean_305_; lean_object* v_elan_x3f_306_; lean_object* v_reservoirApiUrl_307_; lean_object* v_githashOverride_308_; lean_object* v_pkgUrlMap_309_; uint8_t v_noCache_310_; lean_object* v_enableArtifactCache_x3f_311_; lean_object* v_restoreAllArtifacts_x3f_312_; lean_object* v_lakeCache_x3f_313_; lean_object* v_lakeSystemCache_x3f_314_; lean_object* v_lakeConfig_x3f_315_; lean_object* v_cacheKey_x3f_316_; lean_object* v_cacheArtifactEndpoint_x3f_317_; lean_object* v_cacheRevisionEndpoint_x3f_318_; lean_object* v_cacheService_x3f_319_; lean_object* v_initLeanPath_320_; lean_object* v_initLeanSrcPath_321_; lean_object* v_initSharedLibPath_322_; lean_object* v_initPath_323_; lean_object* v_toolchain_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_266_);
lean_dec(v_val_264_);
v_lake_304_ = lean_ctor_get(v_env_217_, 0);
v_lean_305_ = lean_ctor_get(v_env_217_, 1);
v_elan_x3f_306_ = lean_ctor_get(v_env_217_, 2);
v_reservoirApiUrl_307_ = lean_ctor_get(v_env_217_, 3);
v_githashOverride_308_ = lean_ctor_get(v_env_217_, 4);
v_pkgUrlMap_309_ = lean_ctor_get(v_env_217_, 5);
v_noCache_310_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20);
v_enableArtifactCache_x3f_311_ = lean_ctor_get(v_env_217_, 6);
v_restoreAllArtifacts_x3f_312_ = lean_ctor_get(v_env_217_, 7);
v_lakeCache_x3f_313_ = lean_ctor_get(v_env_217_, 8);
v_lakeSystemCache_x3f_314_ = lean_ctor_get(v_env_217_, 9);
v_lakeConfig_x3f_315_ = lean_ctor_get(v_env_217_, 10);
v_cacheKey_x3f_316_ = lean_ctor_get(v_env_217_, 11);
v_cacheArtifactEndpoint_x3f_317_ = lean_ctor_get(v_env_217_, 12);
v_cacheRevisionEndpoint_x3f_318_ = lean_ctor_get(v_env_217_, 13);
v_cacheService_x3f_319_ = lean_ctor_get(v_env_217_, 14);
v_initLeanPath_320_ = lean_ctor_get(v_env_217_, 15);
v_initLeanSrcPath_321_ = lean_ctor_get(v_env_217_, 16);
v_initSharedLibPath_322_ = lean_ctor_get(v_env_217_, 17);
v_initPath_323_ = lean_ctor_get(v_env_217_, 18);
v_toolchain_324_ = lean_ctor_get(v_env_217_, 19);
v_isSharedCheck_332_ = !lean_is_exclusive(v_env_217_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_env_217_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_toolchain_324_);
lean_inc(v_initPath_323_);
lean_inc(v_initSharedLibPath_322_);
lean_inc(v_initLeanSrcPath_321_);
lean_inc(v_initLeanPath_320_);
lean_inc(v_cacheService_x3f_319_);
lean_inc(v_cacheRevisionEndpoint_x3f_318_);
lean_inc(v_cacheArtifactEndpoint_x3f_317_);
lean_inc(v_cacheKey_x3f_316_);
lean_inc(v_lakeConfig_x3f_315_);
lean_inc(v_lakeSystemCache_x3f_314_);
lean_inc(v_lakeCache_x3f_313_);
lean_inc(v_restoreAllArtifacts_x3f_312_);
lean_inc(v_enableArtifactCache_x3f_311_);
lean_inc(v_pkgUrlMap_309_);
lean_inc(v_githashOverride_308_);
lean_inc(v_reservoirApiUrl_307_);
lean_inc(v_elan_x3f_306_);
lean_inc(v_lean_305_);
lean_inc(v_lake_304_);
lean_dec(v_env_217_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_lake_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_lean_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_elan_x3f_306_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_reservoirApiUrl_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_githashOverride_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_pkgUrlMap_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_enableArtifactCache_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_restoreAllArtifacts_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_lakeCache_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_331_, 9, v_lakeSystemCache_x3f_314_);
lean_ctor_set(v_reuseFailAlloc_331_, 10, v_lakeConfig_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_331_, 11, v_cacheKey_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_331_, 12, v_cacheArtifactEndpoint_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_331_, 13, v_cacheRevisionEndpoint_x3f_318_);
lean_ctor_set(v_reuseFailAlloc_331_, 14, v_cacheService_x3f_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 15, v_initLeanPath_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 16, v_initLeanSrcPath_321_);
lean_ctor_set(v_reuseFailAlloc_331_, 17, v_initSharedLibPath_322_);
lean_ctor_set(v_reuseFailAlloc_331_, 18, v_initPath_323_);
lean_ctor_set(v_reuseFailAlloc_331_, 19, v_toolchain_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*20, v_noCache_310_);
v___x_329_ = v_reuseFailAlloc_331_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*20 + 1, v___x_270_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
}
}
else
{
lean_dec(v___x_220_);
if (lean_obj_tag(v_elan_x3f_214_) == 0)
{
goto v___jp_221_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_390_; 
v_val_334_ = lean_ctor_get(v_elan_x3f_214_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_elan_x3f_214_);
if (v_isSharedCheck_390_ == 0)
{
v___x_336_ = v_elan_x3f_214_;
v_isShared_337_ = v_isSharedCheck_390_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v_elan_x3f_214_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_390_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_338_ = lean_string_utf8_byte_size(v_toolchain_216_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
v___x_341_ = lean_bool_not(v___x_340_);
if (v___x_341_ == 0)
{
lean_del_object(v___x_336_);
lean_dec(v_val_334_);
goto v___jp_221_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_215_);
v___x_343_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_334_, v_toolchain_216_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_343_);
v___x_345_ = v___x_336_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_389_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___y_347_; 
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
v___y_347_ = v___x_378_;
goto v___jp_346_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_388_; 
v_val_379_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_388_ == 0)
{
v___x_381_ = v___x_342_;
v_isShared_382_ = v_isSharedCheck_388_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_val_379_);
lean_dec(v___x_342_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_388_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_384_ = l_System_FilePath_join(v_val_379_, v___x_383_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_384_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v___y_347_ = v___x_386_;
goto v___jp_346_;
}
}
}
v___jp_346_:
{
lean_object* v_lake_348_; lean_object* v_lean_349_; lean_object* v_elan_x3f_350_; lean_object* v_reservoirApiUrl_351_; lean_object* v_githashOverride_352_; lean_object* v_pkgUrlMap_353_; uint8_t v_noCache_354_; lean_object* v_enableArtifactCache_x3f_355_; lean_object* v_restoreAllArtifacts_x3f_356_; uint8_t v_noSystemCache_357_; lean_object* v_lakeConfig_x3f_358_; lean_object* v_cacheKey_x3f_359_; lean_object* v_cacheArtifactEndpoint_x3f_360_; lean_object* v_cacheRevisionEndpoint_x3f_361_; lean_object* v_cacheService_x3f_362_; lean_object* v_initLeanPath_363_; lean_object* v_initLeanSrcPath_364_; lean_object* v_initSharedLibPath_365_; lean_object* v_initPath_366_; lean_object* v_toolchain_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_lake_348_ = lean_ctor_get(v_env_217_, 0);
v_lean_349_ = lean_ctor_get(v_env_217_, 1);
v_elan_x3f_350_ = lean_ctor_get(v_env_217_, 2);
v_reservoirApiUrl_351_ = lean_ctor_get(v_env_217_, 3);
v_githashOverride_352_ = lean_ctor_get(v_env_217_, 4);
v_pkgUrlMap_353_ = lean_ctor_get(v_env_217_, 5);
v_noCache_354_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20);
v_enableArtifactCache_x3f_355_ = lean_ctor_get(v_env_217_, 6);
v_restoreAllArtifacts_x3f_356_ = lean_ctor_get(v_env_217_, 7);
v_noSystemCache_357_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_358_ = lean_ctor_get(v_env_217_, 10);
v_cacheKey_x3f_359_ = lean_ctor_get(v_env_217_, 11);
v_cacheArtifactEndpoint_x3f_360_ = lean_ctor_get(v_env_217_, 12);
v_cacheRevisionEndpoint_x3f_361_ = lean_ctor_get(v_env_217_, 13);
v_cacheService_x3f_362_ = lean_ctor_get(v_env_217_, 14);
v_initLeanPath_363_ = lean_ctor_get(v_env_217_, 15);
v_initLeanSrcPath_364_ = lean_ctor_get(v_env_217_, 16);
v_initSharedLibPath_365_ = lean_ctor_get(v_env_217_, 17);
v_initPath_366_ = lean_ctor_get(v_env_217_, 18);
v_toolchain_367_ = lean_ctor_get(v_env_217_, 19);
v_isSharedCheck_375_ = !lean_is_exclusive(v_env_217_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_env_217_, 9);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_env_217_, 8);
lean_dec(v_unused_377_);
v___x_369_ = v_env_217_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_toolchain_367_);
lean_inc(v_initPath_366_);
lean_inc(v_initSharedLibPath_365_);
lean_inc(v_initLeanSrcPath_364_);
lean_inc(v_initLeanPath_363_);
lean_inc(v_cacheService_x3f_362_);
lean_inc(v_cacheRevisionEndpoint_x3f_361_);
lean_inc(v_cacheArtifactEndpoint_x3f_360_);
lean_inc(v_cacheKey_x3f_359_);
lean_inc(v_lakeConfig_x3f_358_);
lean_inc(v_restoreAllArtifacts_x3f_356_);
lean_inc(v_enableArtifactCache_x3f_355_);
lean_inc(v_pkgUrlMap_353_);
lean_inc(v_githashOverride_352_);
lean_inc(v_reservoirApiUrl_351_);
lean_inc(v_elan_x3f_350_);
lean_inc(v_lean_349_);
lean_inc(v_lake_348_);
lean_dec(v_env_217_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 9, v___y_347_);
lean_ctor_set(v___x_369_, 8, v___x_345_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_lake_348_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_lean_349_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_elan_x3f_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_reservoirApiUrl_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_githashOverride_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_pkgUrlMap_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 6, v_enableArtifactCache_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 7, v_restoreAllArtifacts_x3f_356_);
lean_ctor_set(v_reuseFailAlloc_374_, 8, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_374_, 9, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_374_, 10, v_lakeConfig_x3f_358_);
lean_ctor_set(v_reuseFailAlloc_374_, 11, v_cacheKey_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_374_, 12, v_cacheArtifactEndpoint_x3f_360_);
lean_ctor_set(v_reuseFailAlloc_374_, 13, v_cacheRevisionEndpoint_x3f_361_);
lean_ctor_set(v_reuseFailAlloc_374_, 14, v_cacheService_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 15, v_initLeanPath_363_);
lean_ctor_set(v_reuseFailAlloc_374_, 16, v_initLeanSrcPath_364_);
lean_ctor_set(v_reuseFailAlloc_374_, 17, v_initSharedLibPath_365_);
lean_ctor_set(v_reuseFailAlloc_374_, 18, v_initPath_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 19, v_toolchain_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*20, v_noCache_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*20 + 1, v_noSystemCache_357_);
v___x_372_ = v_reuseFailAlloc_374_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_215_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_env_217_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_263_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_263_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_263_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_val_224_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_263_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_lake_228_; lean_object* v_lean_229_; lean_object* v_elan_x3f_230_; lean_object* v_reservoirApiUrl_231_; lean_object* v_githashOverride_232_; lean_object* v_pkgUrlMap_233_; uint8_t v_noCache_234_; lean_object* v_enableArtifactCache_x3f_235_; lean_object* v_restoreAllArtifacts_x3f_236_; uint8_t v_noSystemCache_237_; lean_object* v_lakeConfig_x3f_238_; lean_object* v_cacheKey_x3f_239_; lean_object* v_cacheArtifactEndpoint_x3f_240_; lean_object* v_cacheRevisionEndpoint_x3f_241_; lean_object* v_cacheService_x3f_242_; lean_object* v_initLeanPath_243_; lean_object* v_initLeanSrcPath_244_; lean_object* v_initSharedLibPath_245_; lean_object* v_initPath_246_; lean_object* v_toolchain_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_260_; 
v_lake_228_ = lean_ctor_get(v_env_217_, 0);
v_lean_229_ = lean_ctor_get(v_env_217_, 1);
v_elan_x3f_230_ = lean_ctor_get(v_env_217_, 2);
v_reservoirApiUrl_231_ = lean_ctor_get(v_env_217_, 3);
v_githashOverride_232_ = lean_ctor_get(v_env_217_, 4);
v_pkgUrlMap_233_ = lean_ctor_get(v_env_217_, 5);
v_noCache_234_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20);
v_enableArtifactCache_x3f_235_ = lean_ctor_get(v_env_217_, 6);
v_restoreAllArtifacts_x3f_236_ = lean_ctor_get(v_env_217_, 7);
v_noSystemCache_237_ = lean_ctor_get_uint8(v_env_217_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_238_ = lean_ctor_get(v_env_217_, 10);
v_cacheKey_x3f_239_ = lean_ctor_get(v_env_217_, 11);
v_cacheArtifactEndpoint_x3f_240_ = lean_ctor_get(v_env_217_, 12);
v_cacheRevisionEndpoint_x3f_241_ = lean_ctor_get(v_env_217_, 13);
v_cacheService_x3f_242_ = lean_ctor_get(v_env_217_, 14);
v_initLeanPath_243_ = lean_ctor_get(v_env_217_, 15);
v_initLeanSrcPath_244_ = lean_ctor_get(v_env_217_, 16);
v_initSharedLibPath_245_ = lean_ctor_get(v_env_217_, 17);
v_initPath_246_ = lean_ctor_get(v_env_217_, 18);
v_toolchain_247_ = lean_ctor_get(v_env_217_, 19);
v_isSharedCheck_260_ = !lean_is_exclusive(v_env_217_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_261_ = lean_ctor_get(v_env_217_, 9);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_env_217_, 8);
lean_dec(v_unused_262_);
v___x_249_ = v_env_217_;
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_toolchain_247_);
lean_inc(v_initPath_246_);
lean_inc(v_initSharedLibPath_245_);
lean_inc(v_initLeanSrcPath_244_);
lean_inc(v_initLeanPath_243_);
lean_inc(v_cacheService_x3f_242_);
lean_inc(v_cacheRevisionEndpoint_x3f_241_);
lean_inc(v_cacheArtifactEndpoint_x3f_240_);
lean_inc(v_cacheKey_x3f_239_);
lean_inc(v_lakeConfig_x3f_238_);
lean_inc(v_restoreAllArtifacts_x3f_236_);
lean_inc(v_enableArtifactCache_x3f_235_);
lean_inc(v_pkgUrlMap_233_);
lean_inc(v_githashOverride_232_);
lean_inc(v_reservoirApiUrl_231_);
lean_inc(v_elan_x3f_230_);
lean_inc(v_lean_229_);
lean_inc(v_lake_228_);
lean_dec(v_env_217_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_252_ = l_System_FilePath_join(v_val_224_, v___x_251_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_252_);
v___x_254_ = v___x_226_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_259_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
lean_inc_ref(v___x_254_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 9, v___x_254_);
lean_ctor_set(v___x_249_, 8, v___x_254_);
v___x_256_ = v___x_249_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_lake_228_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_lean_229_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_elan_x3f_230_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_reservoirApiUrl_231_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_githashOverride_232_);
lean_ctor_set(v_reuseFailAlloc_258_, 5, v_pkgUrlMap_233_);
lean_ctor_set(v_reuseFailAlloc_258_, 6, v_enableArtifactCache_x3f_235_);
lean_ctor_set(v_reuseFailAlloc_258_, 7, v_restoreAllArtifacts_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_258_, 8, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_258_, 9, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_258_, 10, v_lakeConfig_x3f_238_);
lean_ctor_set(v_reuseFailAlloc_258_, 11, v_cacheKey_x3f_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 12, v_cacheArtifactEndpoint_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 13, v_cacheRevisionEndpoint_x3f_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 14, v_cacheService_x3f_242_);
lean_ctor_set(v_reuseFailAlloc_258_, 15, v_initLeanPath_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 16, v_initLeanSrcPath_244_);
lean_ctor_set(v_reuseFailAlloc_258_, 17, v_initSharedLibPath_245_);
lean_ctor_set(v_reuseFailAlloc_258_, 18, v_initPath_246_);
lean_ctor_set(v_reuseFailAlloc_258_, 19, v_toolchain_247_);
lean_ctor_set_uint8(v_reuseFailAlloc_258_, sizeof(void*)*20, v_noCache_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_258_, sizeof(void*)*20 + 1, v_noSystemCache_237_);
v___x_256_ = v_reuseFailAlloc_258_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* v_elan_x3f_391_, lean_object* v_userHome_x3f_392_, lean_object* v_toolchain_393_, lean_object* v_env_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_391_, v_userHome_x3f_392_, v_toolchain_393_, v_env_394_);
lean_dec_ref(v_toolchain_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* v_init_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v_k_402_; lean_object* v_v_403_; lean_object* v_l_404_; lean_object* v_r_405_; lean_object* v___x_406_; 
v_k_402_ = lean_ctor_get(v_x_401_, 1);
lean_inc(v_k_402_);
v_v_403_ = lean_ctor_get(v_x_401_, 2);
lean_inc(v_v_403_);
v_l_404_ = lean_ctor_get(v_x_401_, 3);
lean_inc(v_l_404_);
v_r_405_ = lean_ctor_get(v_x_401_, 4);
lean_inc(v_r_405_);
lean_dec_ref_known(v_x_401_, 5);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v_init_400_, v_l_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec(v_r_405_);
lean_dec(v_v_403_);
lean_dec(v_k_402_);
return v___x_406_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_447_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_447_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_447_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_447_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
v___x_412_ = lean_string_dec_eq(v_k_402_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v_n_413_; uint8_t v___x_414_; 
lean_inc(v_k_402_);
v_n_413_ = l_String_toName(v_k_402_);
v___x_414_ = l_Lean_Name_isAnonymous(v_n_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_del_object(v___x_409_);
lean_dec(v_k_402_);
v___x_415_ = l_Lean_Json_getStr_x3f(v_v_403_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_n_413_);
lean_dec(v_a_407_);
lean_dec(v_r_405_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_415_, 1);
v___x_425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_413_, v_a_424_, v_a_407_);
v_init_400_ = v___x_425_;
v_x_401_ = v_r_405_;
goto _start;
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v_n_413_);
lean_dec(v_a_407_);
lean_dec(v_r_405_);
lean_dec(v_v_403_);
v___x_427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
v___x_428_ = lean_string_append(v___x_427_, v_k_402_);
lean_dec(v_k_402_);
v___x_429_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_430_);
v___x_432_ = v___x_409_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v___x_434_; 
lean_del_object(v___x_409_);
lean_dec(v_k_402_);
v___x_434_ = l_Lean_Json_getStr_x3f(v_v_403_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_a_407_);
lean_dec(v_r_405_);
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_434_, 1);
v___x_444_ = lean_box(0);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_444_, v_a_443_, v_a_407_);
v_init_400_ = v___x_445_;
v_x_401_ = v_r_405_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_init_400_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 5)
{
lean_object* v_kvPairs_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_kvPairs_451_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_kvPairs_451_);
lean_dec_ref_known(v_x_450_, 1);
v___x_452_ = lean_box(1);
v___x_453_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v___x_452_, v_kvPairs_451_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_454_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0));
v___x_455_ = lean_unsigned_to_nat(80u);
v___x_456_ = l_Lean_Json_pretty(v_x_450_, v___x_455_);
v___x_457_ = lean_string_append(v___x_454_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap(){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_a_467_; 
v___x_464_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_465_ = lean_io_getenv(v___x_464_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_472_; 
v_val_471_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_465_, 1);
v___x_472_ = l_Lean_Json_parse(v_val_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v_a_467_ = v_a_473_;
goto v___jp_466_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_472_, 1);
v___x_475_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(v_a_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v_a_467_ = v_a_476_;
goto v___jp_466_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 0);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_465_);
v___x_485_ = lean_box(1);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
v___jp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1));
v___x_469_ = lean_string_append(v___x_468_, v_a_467_);
lean_dec_ref(v_a_467_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* v_url_489_){
_start:
{
uint32_t v___y_491_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_string_utf8_byte_size(v_url_489_);
lean_inc_ref(v_url_489_);
v___x_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_502_, 0, v_url_489_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
v___x_503_ = l_String_Slice_Pos_prev_x3f(v___x_502_, v___x_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
uint32_t v___x_504_; 
lean_dec_ref_known(v___x_502_, 3);
v___x_504_ = 65;
v___y_491_ = v___x_504_;
goto v___jp_490_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; 
v_val_505_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___x_503_, 1);
v___x_506_ = l_String_Slice_Pos_get_x3f(v___x_502_, v_val_505_);
lean_dec(v_val_505_);
lean_dec_ref_known(v___x_502_, 3);
if (lean_obj_tag(v___x_506_) == 0)
{
uint32_t v___x_507_; 
v___x_507_ = 65;
v___y_491_ = v___x_507_;
goto v___jp_490_;
}
else
{
lean_object* v_val_508_; uint32_t v___x_509_; 
v_val_508_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_506_, 1);
v___x_509_ = lean_unbox_uint32(v_val_508_);
lean_dec(v_val_508_);
v___y_491_ = v___x_509_;
goto v___jp_490_;
}
}
v___jp_490_:
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 47;
v___x_493_ = lean_uint32_dec_eq(v___y_491_, v___x_492_);
if (v___x_493_ == 0)
{
return v_url_489_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_string_utf8_byte_size(v_url_489_);
lean_inc_ref(v_url_489_);
v___x_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_497_, 0, v_url_489_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_496_);
v___x_498_ = l_String_Slice_Pos_prevn(v___x_497_, v___x_496_, v___x_494_);
lean_dec_ref_known(v___x_497_, 3);
v___x_499_ = lean_string_utf8_extract(v_url_489_, v___x_495_, v___x_498_);
lean_dec(v___x_498_);
lean_dec_ref(v_url_489_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* v_lake_528_, lean_object* v_lean_529_, lean_object* v_elan_x3f_530_, lean_object* v_noCache_531_){
_start:
{
lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v_val_705_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; uint8_t v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v_a_821_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_a_853_; 
v___x_850_ = ((lean_object*)(l_Lake_Env_compute___closed__14));
v___x_851_ = lean_io_getenv(v___x_850_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_872_; lean_object* v___x_873_; 
v_val_872_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_851_, 1);
v___x_873_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_872_);
v_a_853_ = v___x_873_;
goto v___jp_852_;
}
else
{
lean_object* v___x_874_; 
lean_dec(v___x_851_);
v___x_874_ = ((lean_object*)(l_Lake_Env_compute___closed__17));
v_a_853_ = v___x_874_;
goto v___jp_852_;
}
v___jp_533_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v___y_536_);
lean_inc_n(v___y_542_, 2);
lean_inc(v_elan_x3f_530_);
v___x_553_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v___x_553_, 0, v_lake_528_);
lean_ctor_set(v___x_553_, 1, v_lean_529_);
lean_ctor_set(v___x_553_, 2, v_elan_x3f_530_);
lean_ctor_set(v___x_553_, 3, v___y_546_);
lean_ctor_set(v___x_553_, 4, v___y_541_);
lean_ctor_set(v___x_553_, 5, v___y_550_);
lean_ctor_set(v___x_553_, 6, v___y_547_);
lean_ctor_set(v___x_553_, 7, v___y_537_);
lean_ctor_set(v___x_553_, 8, v___y_542_);
lean_ctor_set(v___x_553_, 9, v___y_542_);
lean_ctor_set(v___x_553_, 10, v___y_548_);
lean_ctor_set(v___x_553_, 11, v___y_549_);
lean_ctor_set(v___x_553_, 12, v___y_535_);
lean_ctor_set(v___x_553_, 13, v___y_551_);
lean_ctor_set(v___x_553_, 14, v___y_552_);
lean_ctor_set(v___x_553_, 15, v___y_545_);
lean_ctor_set(v___x_553_, 16, v___y_540_);
lean_ctor_set(v___x_553_, 17, v___y_539_);
lean_ctor_set(v___x_553_, 18, v___y_543_);
lean_ctor_set(v___x_553_, 19, v___y_536_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*20, v___y_544_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*20 + 1, v___y_538_);
v___x_554_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_530_, v___y_534_, v___y_536_, v___x_553_);
lean_dec_ref(v___y_536_);
return v___x_554_;
}
v___jp_555_:
{
if (lean_obj_tag(v___y_571_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
v___y_534_ = v___y_556_;
v___y_535_ = v___y_557_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_559_;
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_564_;
v___y_543_ = v___y_565_;
v___y_544_ = v___y_566_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_569_;
v___y_547_ = v___y_568_;
v___y_548_ = v___y_570_;
v___y_549_ = v___y_572_;
v___y_550_ = v___y_573_;
v___y_551_ = v___y_574_;
v___y_552_ = v___x_575_;
goto v___jp_533_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_591_; 
v_val_576_ = lean_ctor_get(v___y_571_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_591_ == 0)
{
v___x_578_ = v___y_571_;
v_isShared_579_ = v_isSharedCheck_591_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v___y_571_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_591_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_str_584_; lean_object* v_startInclusive_585_; lean_object* v_endExclusive_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_string_utf8_byte_size(v_val_576_);
v___x_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_582_, 0, v_val_576_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
lean_ctor_set(v___x_582_, 2, v___x_581_);
v___x_583_ = l_String_Slice_trimAscii(v___x_582_);
v_str_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_str_584_);
v_startInclusive_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_startInclusive_585_);
v_endExclusive_586_ = lean_ctor_get(v___x_583_, 2);
lean_inc(v_endExclusive_586_);
lean_dec_ref(v___x_583_);
v___x_587_ = lean_string_utf8_extract(v_str_584_, v_startInclusive_585_, v_endExclusive_586_);
lean_dec(v_endExclusive_586_);
lean_dec(v_startInclusive_585_);
lean_dec_ref(v_str_584_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_587_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
v___y_534_ = v___y_556_;
v___y_535_ = v___y_557_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_559_;
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_564_;
v___y_543_ = v___y_565_;
v___y_544_ = v___y_566_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_569_;
v___y_547_ = v___y_568_;
v___y_548_ = v___y_570_;
v___y_549_ = v___y_572_;
v___y_550_ = v___y_573_;
v___y_551_ = v___y_574_;
v___y_552_ = v___x_589_;
goto v___jp_533_;
}
}
}
}
v___jp_592_:
{
if (lean_obj_tag(v___y_597_) == 0)
{
v___y_556_ = v___y_593_;
v___y_557_ = v___y_611_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_598_;
v___y_562_ = v___y_599_;
v___y_563_ = v___y_600_;
v___y_564_ = v___y_601_;
v___y_565_ = v___y_602_;
v___y_566_ = v___y_603_;
v___y_567_ = v___y_604_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_605_;
v___y_570_ = v___y_607_;
v___y_571_ = v___y_608_;
v___y_572_ = v___y_609_;
v___y_573_ = v___y_610_;
v___y_574_ = v___y_597_;
goto v___jp_555_;
}
else
{
lean_object* v_val_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_val_612_ = lean_ctor_get(v___y_597_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___y_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___y_597_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_val_612_);
lean_dec(v___y_597_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v___y_556_ = v___y_593_;
v___y_557_ = v___y_611_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_598_;
v___y_562_ = v___y_599_;
v___y_563_ = v___y_600_;
v___y_564_ = v___y_601_;
v___y_565_ = v___y_602_;
v___y_566_ = v___y_603_;
v___y_567_ = v___y_604_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_605_;
v___y_570_ = v___y_607_;
v___y_571_ = v___y_608_;
v___y_572_ = v___y_609_;
v___y_573_ = v___y_610_;
v___y_574_ = v___x_618_;
goto v___jp_555_;
}
}
}
}
v___jp_621_:
{
if (lean_obj_tag(v___y_622_) == 0)
{
v___y_593_ = v___y_623_;
v___y_594_ = v___y_624_;
v___y_595_ = v___y_625_;
v___y_596_ = v___y_626_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_628_;
v___y_599_ = v___y_629_;
v___y_600_ = v___y_630_;
v___y_601_ = v___y_631_;
v___y_602_ = v___y_632_;
v___y_603_ = v___y_633_;
v___y_604_ = v___y_634_;
v___y_605_ = v___y_636_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_637_;
v___y_608_ = v___y_638_;
v___y_609_ = v___y_640_;
v___y_610_ = v___y_639_;
v___y_611_ = v___y_622_;
goto v___jp_592_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_val_641_ = lean_ctor_get(v___y_622_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___y_622_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v___y_622_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___y_622_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_593_ = v___y_623_;
v___y_594_ = v___y_624_;
v___y_595_ = v___y_625_;
v___y_596_ = v___y_626_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_628_;
v___y_599_ = v___y_629_;
v___y_600_ = v___y_630_;
v___y_601_ = v___y_631_;
v___y_602_ = v___y_632_;
v___y_603_ = v___y_633_;
v___y_604_ = v___y_634_;
v___y_605_ = v___y_636_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_637_;
v___y_608_ = v___y_638_;
v___y_609_ = v___y_640_;
v___y_610_ = v___y_639_;
v___y_611_ = v___x_647_;
goto v___jp_592_;
}
}
}
}
v___jp_650_:
{
if (lean_obj_tag(v___y_666_) == 0)
{
v___y_622_ = v___y_651_;
v___y_623_ = v___y_652_;
v___y_624_ = v___y_653_;
v___y_625_ = v___y_654_;
v___y_626_ = v___y_655_;
v___y_627_ = v___y_656_;
v___y_628_ = v___y_657_;
v___y_629_ = v___y_658_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_660_;
v___y_632_ = v___y_661_;
v___y_633_ = v___y_663_;
v___y_634_ = v___y_662_;
v___y_635_ = v___y_665_;
v___y_636_ = v___y_664_;
v___y_637_ = v___y_669_;
v___y_638_ = v___y_667_;
v___y_639_ = v___y_668_;
v___y_640_ = v___y_666_;
goto v___jp_621_;
}
else
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_685_; 
v_val_670_ = lean_ctor_get(v___y_666_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___y_666_);
if (v_isSharedCheck_685_ == 0)
{
v___x_672_ = v___y_666_;
v_isShared_673_ = v_isSharedCheck_685_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___y_666_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_685_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_str_678_; lean_object* v_startInclusive_679_; lean_object* v_endExclusive_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_string_utf8_byte_size(v_val_670_);
v___x_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_676_, 0, v_val_670_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
lean_ctor_set(v___x_676_, 2, v___x_675_);
v___x_677_ = l_String_Slice_trimAscii(v___x_676_);
v_str_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_str_678_);
v_startInclusive_679_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_startInclusive_679_);
v_endExclusive_680_ = lean_ctor_get(v___x_677_, 2);
lean_inc(v_endExclusive_680_);
lean_dec_ref(v___x_677_);
v___x_681_ = lean_string_utf8_extract(v_str_678_, v_startInclusive_679_, v_endExclusive_680_);
lean_dec(v_endExclusive_680_);
lean_dec(v_startInclusive_679_);
lean_dec_ref(v_str_678_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_681_);
v___x_683_ = v___x_672_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v___y_622_ = v___y_651_;
v___y_623_ = v___y_652_;
v___y_624_ = v___y_653_;
v___y_625_ = v___y_654_;
v___y_626_ = v___y_655_;
v___y_627_ = v___y_656_;
v___y_628_ = v___y_657_;
v___y_629_ = v___y_658_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_660_;
v___y_632_ = v___y_661_;
v___y_633_ = v___y_663_;
v___y_634_ = v___y_662_;
v___y_635_ = v___y_665_;
v___y_636_ = v___y_664_;
v___y_637_ = v___y_669_;
v___y_638_ = v___y_667_;
v___y_639_ = v___y_668_;
v___y_640_ = v___x_683_;
goto v___jp_621_;
}
}
}
}
v___jp_686_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_val_705_);
v___y_651_ = v___y_687_;
v___y_652_ = v___y_688_;
v___y_653_ = v___y_689_;
v___y_654_ = v___y_690_;
v___y_655_ = v___y_691_;
v___y_656_ = v___y_692_;
v___y_657_ = v___y_693_;
v___y_658_ = v___y_694_;
v___y_659_ = v___y_695_;
v___y_660_ = v___y_696_;
v___y_661_ = v___y_697_;
v___y_662_ = v___y_699_;
v___y_663_ = v___y_698_;
v___y_664_ = v___y_701_;
v___y_665_ = v___y_700_;
v___y_666_ = v___y_702_;
v___y_667_ = v___y_703_;
v___y_668_ = v___y_704_;
v___y_669_ = v___x_706_;
goto v___jp_650_;
}
v___jp_707_:
{
uint8_t v___x_725_; lean_object* v___x_726_; 
v___x_725_ = 0;
v___x_726_ = lean_box(0);
if (lean_obj_tag(v___y_708_) == 0)
{
if (lean_obj_tag(v___y_710_) == 0)
{
v___y_651_ = v___y_709_;
v___y_652_ = v___y_710_;
v___y_653_ = v___y_711_;
v___y_654_ = v___y_724_;
v___y_655_ = v___x_725_;
v___y_656_ = v___y_712_;
v___y_657_ = v___y_713_;
v___y_658_ = v___y_714_;
v___y_659_ = v___y_715_;
v___y_660_ = v___x_726_;
v___y_661_ = v___y_716_;
v___y_662_ = v___y_717_;
v___y_663_ = v___y_718_;
v___y_664_ = v___y_719_;
v___y_665_ = v___y_720_;
v___y_666_ = v___y_721_;
v___y_667_ = v___y_722_;
v___y_668_ = v___y_723_;
v___y_669_ = v___y_710_;
goto v___jp_650_;
}
else
{
lean_object* v_val_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_val_727_ = lean_ctor_get(v___y_710_, 0);
v___x_728_ = ((lean_object*)(l_Lake_Env_compute___closed__0));
lean_inc(v_val_727_);
v___x_729_ = l_System_FilePath_join(v_val_727_, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lake_Env_compute___closed__1));
v___x_731_ = l_System_FilePath_join(v___x_729_, v___x_730_);
v___y_687_ = v___y_709_;
v___y_688_ = v___y_710_;
v___y_689_ = v___y_711_;
v___y_690_ = v___y_724_;
v___y_691_ = v___x_725_;
v___y_692_ = v___y_712_;
v___y_693_ = v___y_713_;
v___y_694_ = v___y_714_;
v___y_695_ = v___y_715_;
v___y_696_ = v___x_726_;
v___y_697_ = v___y_716_;
v___y_698_ = v___y_718_;
v___y_699_ = v___y_717_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_719_;
v___y_702_ = v___y_721_;
v___y_703_ = v___y_722_;
v___y_704_ = v___y_723_;
v_val_705_ = v___x_731_;
goto v___jp_686_;
}
}
else
{
lean_object* v_val_732_; 
v_val_732_ = lean_ctor_get(v___y_708_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v___y_708_, 1);
v___y_687_ = v___y_709_;
v___y_688_ = v___y_710_;
v___y_689_ = v___y_711_;
v___y_690_ = v___y_724_;
v___y_691_ = v___x_725_;
v___y_692_ = v___y_712_;
v___y_693_ = v___y_713_;
v___y_694_ = v___y_714_;
v___y_695_ = v___y_715_;
v___y_696_ = v___x_726_;
v___y_697_ = v___y_716_;
v___y_698_ = v___y_718_;
v___y_699_ = v___y_717_;
v___y_700_ = v___y_720_;
v___y_701_ = v___y_719_;
v___y_702_ = v___y_721_;
v___y_703_ = v___y_722_;
v___y_704_ = v___y_723_;
v_val_705_ = v_val_732_;
goto v___jp_686_;
}
}
v___jp_733_:
{
if (lean_obj_tag(v___y_742_) == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_box(0);
v___y_708_ = v___y_734_;
v___y_709_ = v___y_735_;
v___y_710_ = v___y_736_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_738_;
v___y_713_ = v___y_739_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_743_;
v___y_717_ = v___y_744_;
v___y_718_ = v___y_745_;
v___y_719_ = v___y_746_;
v___y_720_ = v___y_750_;
v___y_721_ = v___y_747_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_749_;
v___y_724_ = v___x_751_;
goto v___jp_707_;
}
else
{
lean_object* v_val_752_; lean_object* v___x_753_; 
v_val_752_ = lean_ctor_get(v___y_742_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___y_742_, 1);
v___x_753_ = l_Lake_envToBool_x3f(v_val_752_);
v___y_708_ = v___y_734_;
v___y_709_ = v___y_735_;
v___y_710_ = v___y_736_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_738_;
v___y_713_ = v___y_739_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_743_;
v___y_717_ = v___y_744_;
v___y_718_ = v___y_745_;
v___y_719_ = v___y_746_;
v___y_720_ = v___y_750_;
v___y_721_ = v___y_747_;
v___y_722_ = v___y_748_;
v___y_723_ = v___y_749_;
v___y_724_ = v___x_753_;
goto v___jp_707_;
}
}
v___jp_754_:
{
if (lean_obj_tag(v___y_767_) == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_box(0);
v___y_734_ = v___y_755_;
v___y_735_ = v___y_756_;
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v___y_765_;
v___y_745_ = v___y_771_;
v___y_746_ = v___y_766_;
v___y_747_ = v___y_768_;
v___y_748_ = v___y_769_;
v___y_749_ = v___y_770_;
v___y_750_ = v___x_772_;
goto v___jp_733_;
}
else
{
lean_object* v_val_773_; lean_object* v___x_774_; 
v_val_773_ = lean_ctor_get(v___y_767_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___y_767_, 1);
v___x_774_ = l_Lake_envToBool_x3f(v_val_773_);
v___y_734_ = v___y_755_;
v___y_735_ = v___y_756_;
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v___y_765_;
v___y_745_ = v___y_771_;
v___y_746_ = v___y_766_;
v___y_747_ = v___y_768_;
v___y_748_ = v___y_769_;
v___y_749_ = v___y_770_;
v___y_750_ = v___x_774_;
goto v___jp_733_;
}
}
v___jp_775_:
{
uint8_t v___x_792_; 
v___x_792_ = 0;
v___y_755_ = v___y_776_;
v___y_756_ = v___y_777_;
v___y_757_ = v___y_778_;
v___y_758_ = v___y_779_;
v___y_759_ = v___y_780_;
v___y_760_ = v___y_781_;
v___y_761_ = v___y_782_;
v___y_762_ = v___y_783_;
v___y_763_ = v___y_784_;
v___y_764_ = v___y_785_;
v___y_765_ = v___y_786_;
v___y_766_ = v___y_787_;
v___y_767_ = v___y_788_;
v___y_768_ = v___y_789_;
v___y_769_ = v___y_790_;
v___y_770_ = v___y_791_;
v___y_771_ = v___x_792_;
goto v___jp_754_;
}
v___jp_793_:
{
if (lean_obj_tag(v_noCache_531_) == 0)
{
if (lean_obj_tag(v___y_806_) == 0)
{
v___y_776_ = v___y_794_;
v___y_777_ = v___y_795_;
v___y_778_ = v___y_796_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_810_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_807_;
v___y_790_ = v___y_808_;
v___y_791_ = v___y_809_;
goto v___jp_775_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_812_; 
v_val_811_ = lean_ctor_get(v___y_806_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___y_806_, 1);
v___x_812_ = l_Lake_envToBool_x3f(v_val_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
v___y_776_ = v___y_794_;
v___y_777_ = v___y_795_;
v___y_778_ = v___y_796_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_810_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_807_;
v___y_790_ = v___y_808_;
v___y_791_ = v___y_809_;
goto v___jp_775_;
}
else
{
lean_object* v_val_813_; uint8_t v___x_814_; 
v_val_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_unbox(v_val_813_);
lean_dec(v_val_813_);
v___y_755_ = v___y_794_;
v___y_756_ = v___y_795_;
v___y_757_ = v___y_796_;
v___y_758_ = v___y_797_;
v___y_759_ = v___y_798_;
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_801_;
v___y_764_ = v___y_802_;
v___y_765_ = v___y_803_;
v___y_766_ = v___y_804_;
v___y_767_ = v___y_805_;
v___y_768_ = v___y_807_;
v___y_769_ = v___y_808_;
v___y_770_ = v___y_809_;
v___y_771_ = v___x_814_;
goto v___jp_754_;
}
}
}
else
{
lean_object* v_val_815_; uint8_t v___x_816_; 
lean_dec(v___y_806_);
v_val_815_ = lean_ctor_get(v_noCache_531_, 0);
v___x_816_ = lean_unbox(v_val_815_);
v___y_755_ = v___y_794_;
v___y_756_ = v___y_795_;
v___y_757_ = v___y_796_;
v___y_758_ = v___y_797_;
v___y_759_ = v___y_798_;
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_801_;
v___y_764_ = v___y_802_;
v___y_765_ = v___y_803_;
v___y_766_ = v___y_804_;
v___y_767_ = v___y_805_;
v___y_768_ = v___y_807_;
v___y_769_ = v___y_808_;
v___y_770_ = v___y_809_;
v___y_771_ = v___x_816_;
goto v___jp_754_;
}
}
v___jp_817_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_822_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
v___x_823_ = lean_io_getenv(v___x_822_);
v___x_824_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
v___x_825_ = lean_io_getenv(v___x_824_);
v___x_826_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
v___x_827_ = lean_io_getenv(v___x_826_);
v___x_828_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
v___x_829_ = lean_io_getenv(v___x_828_);
v___x_830_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_831_ = lean_io_getenv(v___x_830_);
v___x_832_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_833_ = lean_io_getenv(v___x_832_);
v___x_834_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_835_ = lean_io_getenv(v___x_834_);
v___x_836_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
v___x_837_ = lean_io_getenv(v___x_836_);
v___x_838_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_839_ = lean_io_getenv(v___x_838_);
v___x_840_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_841_ = l_Lake_getSearchPath(v___x_840_);
v___x_842_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_843_ = l_Lake_getSearchPath(v___x_842_);
v___x_844_ = l_Lake_sharedLibPathEnvVar;
v___x_845_ = l_Lake_getSearchPath(v___x_844_);
v___x_846_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_847_ = l_Lake_getSearchPath(v___x_846_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___y_794_ = v___x_829_;
v___y_795_ = v___x_833_;
v___y_796_ = v___y_818_;
v___y_797_ = v___y_819_;
v___y_798_ = v___x_835_;
v___y_799_ = v___x_845_;
v___y_800_ = v___x_843_;
v___y_801_ = v___x_827_;
v___y_802_ = v___x_847_;
v___y_803_ = v___x_841_;
v___y_804_ = v_a_821_;
v___y_805_ = v___x_825_;
v___y_806_ = v___x_823_;
v___y_807_ = v___x_831_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_820_;
v___y_810_ = v___x_848_;
goto v___jp_793_;
}
else
{
lean_object* v_val_849_; 
v_val_849_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___x_839_, 1);
v___y_794_ = v___x_829_;
v___y_795_ = v___x_833_;
v___y_796_ = v___y_818_;
v___y_797_ = v___y_819_;
v___y_798_ = v___x_835_;
v___y_799_ = v___x_845_;
v___y_800_ = v___x_843_;
v___y_801_ = v___x_827_;
v___y_802_ = v___x_847_;
v___y_803_ = v___x_841_;
v___y_804_ = v_a_821_;
v___y_805_ = v___x_825_;
v___y_806_ = v___x_823_;
v___y_807_ = v___x_831_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_820_;
v___y_810_ = v_val_849_;
goto v___jp_793_;
}
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = l_Lake_Env_computeToolchain();
v___x_855_ = l_Lake_getUserHome_x3f();
v___x_856_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = ((lean_object*)(l_Lake_Env_compute___closed__15));
v___x_859_ = lean_io_getenv(v___x_858_);
if (lean_obj_tag(v___x_859_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_861_; 
lean_dec_ref(v_a_853_);
v_val_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_860_);
v___y_818_ = v___x_855_;
v___y_819_ = v___x_854_;
v___y_820_ = v_a_857_;
v_a_821_ = v___x_861_;
goto v___jp_817_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___x_859_);
v___x_862_ = ((lean_object*)(l_Lake_Env_compute___closed__16));
v___x_863_ = lean_string_append(v_a_853_, v___x_862_);
v___y_818_ = v___x_855_;
v___y_819_ = v___x_854_;
v___y_820_ = v_a_857_;
v_a_821_ = v___x_863_;
goto v___jp_817_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_elan_x3f_530_);
lean_dec_ref(v_lean_529_);
lean_dec_ref(v_lake_528_);
v_a_864_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_856_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_856_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* v_lake_875_, lean_object* v_lean_876_, lean_object* v_elan_x3f_877_, lean_object* v_noCache_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lake_Env_compute(v_lake_875_, v_lean_876_, v_elan_x3f_877_, v_noCache_878_);
lean_dec(v_noCache_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object* v_env_881_){
_start:
{
lean_object* v_toolchain_882_; 
v_toolchain_882_ = lean_ctor_get(v_env_881_, 19);
lean_inc_ref(v_toolchain_882_);
return v_toolchain_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object* v_env_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lake_Env_cacheToolchain(v_env_883_);
lean_dec_ref(v_env_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* v_env_885_){
_start:
{
lean_object* v_lean_886_; lean_object* v_githashOverride_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_lean_886_ = lean_ctor_get(v_env_885_, 1);
v_githashOverride_887_ = lean_ctor_get(v_env_885_, 4);
v___x_888_ = lean_string_utf8_byte_size(v_githashOverride_887_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_inc_ref(v_githashOverride_887_);
return v_githashOverride_887_;
}
else
{
lean_object* v_githash_891_; 
v_githash_891_ = lean_ctor_get(v_lean_886_, 1);
lean_inc_ref(v_githash_891_);
return v_githash_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* v_env_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lake_Env_leanGithash(v_env_892_);
lean_dec_ref(v_env_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* v_env_894_){
_start:
{
lean_object* v_lake_895_; lean_object* v_lean_896_; lean_object* v_initPath_897_; lean_object* v_binDir_898_; lean_object* v_binDir_899_; uint8_t v___x_900_; 
v_lake_895_ = lean_ctor_get(v_env_894_, 0);
v_lean_896_ = lean_ctor_get(v_env_894_, 1);
v_initPath_897_ = lean_ctor_get(v_env_894_, 18);
v_binDir_898_ = lean_ctor_get(v_lake_895_, 2);
v_binDir_899_ = lean_ctor_get(v_lean_896_, 6);
v___x_900_ = lean_string_dec_eq(v_binDir_898_, v_binDir_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc(v_initPath_897_);
lean_inc_ref(v_binDir_899_);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v_binDir_899_);
lean_ctor_set(v___x_901_, 1, v_initPath_897_);
lean_inc_ref(v_binDir_898_);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v_binDir_898_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_inc(v_initPath_897_);
lean_inc_ref(v_binDir_899_);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v_binDir_899_);
lean_ctor_set(v___x_903_, 1, v_initPath_897_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* v_env_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lake_Env_path(v_env_904_);
lean_dec_ref(v_env_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* v_env_906_){
_start:
{
lean_object* v_lake_907_; lean_object* v_initLeanPath_908_; lean_object* v_libDir_909_; lean_object* v___x_910_; 
v_lake_907_ = lean_ctor_get(v_env_906_, 0);
v_initLeanPath_908_ = lean_ctor_get(v_env_906_, 15);
v_libDir_909_ = lean_ctor_get(v_lake_907_, 3);
lean_inc(v_initLeanPath_908_);
lean_inc_ref(v_libDir_909_);
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v_libDir_909_);
lean_ctor_set(v___x_910_, 1, v_initLeanPath_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* v_env_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lake_Env_leanPath(v_env_911_);
lean_dec_ref(v_env_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* v_env_913_){
_start:
{
lean_object* v_lake_914_; lean_object* v_initLeanSrcPath_915_; lean_object* v_srcDir_916_; lean_object* v___x_917_; 
v_lake_914_ = lean_ctor_get(v_env_913_, 0);
v_initLeanSrcPath_915_ = lean_ctor_get(v_env_913_, 16);
v_srcDir_916_ = lean_ctor_get(v_lake_914_, 1);
lean_inc(v_initLeanSrcPath_915_);
lean_inc_ref(v_srcDir_916_);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v_srcDir_916_);
lean_ctor_set(v___x_917_, 1, v_initLeanSrcPath_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* v_env_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lake_Env_leanSrcPath(v_env_918_);
lean_dec_ref(v_env_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* v_env_920_){
_start:
{
lean_object* v_lean_921_; lean_object* v_initSharedLibPath_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_lean_921_ = lean_ctor_get(v_env_920_, 1);
lean_inc_ref(v_lean_921_);
v_initSharedLibPath_922_ = lean_ctor_get(v_env_920_, 17);
lean_inc(v_initSharedLibPath_922_);
lean_dec_ref(v_env_920_);
v___x_923_ = l_Lake_LeanInstall_sharedLibPath(v_lean_921_);
lean_dec_ref(v_lean_921_);
v___x_924_ = l_List_appendTR___redArg(v___x_923_, v_initSharedLibPath_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
v___x_956_ = lean_unsigned_to_nat(9u);
v___x_957_ = lean_mk_empty_array_with_capacity(v___x_956_);
v___x_958_ = lean_array_push(v___x_957_, v___x_955_);
return v___x_958_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
v___x_960_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__14, &l_Lake_Env_noToolchainVars___closed__14_once, _init_l_Lake_Env_noToolchainVars___closed__14);
v___x_961_ = lean_array_push(v___x_960_, v___x_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* v_env_964_){
_start:
{
uint8_t v_noSystemCache_965_; lean_object* v_lakeSystemCache_x3f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___y_970_; 
v_noSystemCache_965_ = lean_ctor_get_uint8(v_env_964_, sizeof(void*)*20 + 1);
v_lakeSystemCache_x3f_966_ = lean_ctor_get(v_env_964_, 9);
lean_inc(v_lakeSystemCache_x3f_966_);
lean_dec_ref(v_env_964_);
v___x_967_ = lean_box(0);
v___x_968_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (v_noSystemCache_965_ == 0)
{
if (lean_obj_tag(v_lakeSystemCache_x3f_966_) == 0)
{
v___y_970_ = v___x_967_;
goto v___jp_969_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_val_986_ = lean_ctor_get(v_lakeSystemCache_x3f_966_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_lakeSystemCache_x3f_966_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v_lakeSystemCache_x3f_966_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_val_986_);
lean_dec(v_lakeSystemCache_x3f_966_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v___y_970_ = v___x_991_;
goto v___jp_969_;
}
}
}
}
else
{
lean_object* v___x_994_; 
lean_dec(v_lakeSystemCache_x3f_966_);
v___x_994_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_970_ = v___x_994_;
goto v___jp_969_;
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_968_);
lean_ctor_set(v___x_971_, 1, v___y_970_);
v___x_972_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__4));
v___x_973_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__6));
v___x_974_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__8));
v___x_975_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__9));
v___x_976_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__11));
v___x_977_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__13));
v___x_978_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__15, &l_Lake_Env_noToolchainVars___closed__15_once, _init_l_Lake_Env_noToolchainVars___closed__15);
v___x_979_ = lean_array_push(v___x_978_, v___x_971_);
v___x_980_ = lean_array_push(v___x_979_, v___x_972_);
v___x_981_ = lean_array_push(v___x_980_, v___x_973_);
v___x_982_ = lean_array_push(v___x_981_, v___x_974_);
v___x_983_ = lean_array_push(v___x_982_, v___x_975_);
v___x_984_ = lean_array_push(v___x_983_, v___x_976_);
v___x_985_ = lean_array_push(v___x_984_, v___x_977_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(1);
v___x_997_ = lean_panic_fn_borrowed(v___x_996_, v_msg_995_);
return v___x_997_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_1002_ = lean_unsigned_to_nat(35u);
v___x_1003_ = lean_unsigned_to_nat(182u);
v___x_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1005_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1006_ = l_mkPanicMessageWithDecl(v___x_1005_, v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_);
return v___x_1006_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_1008_ = lean_unsigned_to_nat(21u);
v___x_1009_ = lean_unsigned_to_nat(183u);
v___x_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1011_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1012_ = l_mkPanicMessageWithDecl(v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_);
return v___x_1012_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1016_ = lean_unsigned_to_nat(35u);
v___x_1017_ = lean_unsigned_to_nat(276u);
v___x_1018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1019_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1020_ = l_mkPanicMessageWithDecl(v___x_1019_, v___x_1018_, v___x_1017_, v___x_1016_, v___x_1015_);
return v___x_1020_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1022_ = lean_unsigned_to_nat(21u);
v___x_1023_ = lean_unsigned_to_nat(277u);
v___x_1024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1025_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1026_ = l_mkPanicMessageWithDecl(v___x_1025_, v___x_1024_, v___x_1023_, v___x_1022_, v___x_1021_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* v_k_1027_, lean_object* v_v_1028_, lean_object* v_t_1029_){
_start:
{
if (lean_obj_tag(v_t_1029_) == 0)
{
lean_object* v_size_1030_; lean_object* v_k_1031_; lean_object* v_v_1032_; lean_object* v_l_1033_; lean_object* v_r_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1390_; 
v_size_1030_ = lean_ctor_get(v_t_1029_, 0);
v_k_1031_ = lean_ctor_get(v_t_1029_, 1);
v_v_1032_ = lean_ctor_get(v_t_1029_, 2);
v_l_1033_ = lean_ctor_get(v_t_1029_, 3);
v_r_1034_ = lean_ctor_get(v_t_1029_, 4);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_t_1029_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1036_ = v_t_1029_;
v_isShared_1037_ = v_isSharedCheck_1390_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_r_1034_);
lean_inc(v_l_1033_);
lean_inc(v_v_1032_);
lean_inc(v_k_1031_);
lean_inc(v_size_1030_);
lean_dec(v_t_1029_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1390_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_string_compare(v_k_1027_, v_k_1031_);
switch(v___x_1038_)
{
case 0:
{
lean_object* v___x_1039_; 
lean_dec(v_size_1030_);
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1027_, v_v_1028_, v_l_1033_);
if (lean_obj_tag(v_r_1034_) == 0)
{
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_size_1040_; lean_object* v_size_1041_; lean_object* v_k_1042_; lean_object* v_v_1043_; lean_object* v_l_1044_; lean_object* v_r_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_size_1040_ = lean_ctor_get(v_r_1034_, 0);
v_size_1041_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_size_1041_);
v_k_1042_ = lean_ctor_get(v___x_1039_, 1);
lean_inc(v_k_1042_);
v_v_1043_ = lean_ctor_get(v___x_1039_, 2);
lean_inc(v_v_1043_);
v_l_1044_ = lean_ctor_get(v___x_1039_, 3);
lean_inc(v_l_1044_);
v_r_1045_ = lean_ctor_get(v___x_1039_, 4);
lean_inc(v_r_1045_);
v___x_1046_ = lean_unsigned_to_nat(3u);
v___x_1047_ = lean_nat_mul(v___x_1046_, v_size_1040_);
v___x_1048_ = lean_nat_dec_lt(v___x_1047_, v_size_1041_);
lean_dec(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec(v_r_1045_);
lean_dec(v_l_1044_);
lean_dec(v_v_1043_);
lean_dec(v_k_1042_);
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_add(v___x_1049_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1051_ = lean_nat_add(v___x_1050_, v_size_1040_);
lean_dec(v___x_1050_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1051_);
v___x_1053_ = v___x_1036_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_r_1034_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; lean_object* v_unused_1131_; 
v_unused_1127_ = lean_ctor_get(v___x_1039_, 4);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v___x_1039_, 3);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v___x_1039_, 2);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v___x_1039_, 1);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1131_);
v___x_1056_ = v___x_1039_;
v_isShared_1057_ = v_isSharedCheck_1126_;
goto v_resetjp_1055_;
}
else
{
lean_dec(v___x_1039_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1126_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
if (lean_obj_tag(v_l_1044_) == 0)
{
if (lean_obj_tag(v_r_1045_) == 0)
{
lean_object* v_size_1058_; lean_object* v_size_1059_; lean_object* v_k_1060_; lean_object* v_v_1061_; lean_object* v_l_1062_; lean_object* v_r_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_size_1058_ = lean_ctor_get(v_l_1044_, 0);
v_size_1059_ = lean_ctor_get(v_r_1045_, 0);
v_k_1060_ = lean_ctor_get(v_r_1045_, 1);
v_v_1061_ = lean_ctor_get(v_r_1045_, 2);
v_l_1062_ = lean_ctor_get(v_r_1045_, 3);
v_r_1063_ = lean_ctor_get(v_r_1045_, 4);
v___x_1064_ = lean_unsigned_to_nat(2u);
v___x_1065_ = lean_nat_mul(v___x_1064_, v_size_1058_);
v___x_1066_ = lean_nat_dec_lt(v_size_1059_, v___x_1065_);
lean_dec(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1096_; 
lean_inc(v_r_1063_);
lean_inc(v_l_1062_);
lean_inc(v_v_1061_);
lean_inc(v_k_1060_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_r_1045_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1097_ = lean_ctor_get(v_r_1045_, 4);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_r_1045_, 3);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_r_1045_, 2);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_r_1045_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_r_1045_, 0);
lean_dec(v_unused_1101_);
v___x_1068_ = v_r_1045_;
v_isShared_1069_ = v_isSharedCheck_1096_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_r_1045_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1096_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___x_1084_; lean_object* v___y_1086_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v___x_1070_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1072_ = lean_nat_add(v___x_1071_, v_size_1040_);
lean_dec(v___x_1071_);
v___x_1084_ = lean_nat_add(v___x_1070_, v_size_1058_);
if (lean_obj_tag(v_l_1062_) == 0)
{
lean_object* v_size_1094_; 
v_size_1094_ = lean_ctor_get(v_l_1062_, 0);
lean_inc(v_size_1094_);
v___y_1086_ = v_size_1094_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___y_1086_ = v___x_1095_;
goto v___jp_1085_;
}
v___jp_1073_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_nat_add(v___y_1074_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec(v___y_1074_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v_r_1034_);
lean_ctor_set(v___x_1068_, 3, v_r_1063_);
lean_ctor_set(v___x_1068_, 2, v_v_1032_);
lean_ctor_set(v___x_1068_, 1, v_k_1031_);
lean_ctor_set(v___x_1068_, 0, v___x_1077_);
v___x_1079_ = v___x_1068_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_r_1063_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_r_1034_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1079_);
lean_ctor_set(v___x_1056_, 3, v___y_1075_);
lean_ctor_set(v___x_1056_, 2, v_v_1061_);
lean_ctor_set(v___x_1056_, 1, v_k_1060_);
lean_ctor_set(v___x_1056_, 0, v___x_1072_);
v___x_1081_ = v___x_1056_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v___y_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_nat_add(v___x_1084_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec(v___x_1084_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_l_1062_);
lean_ctor_set(v___x_1036_, 3, v_l_1044_);
lean_ctor_set(v___x_1036_, 2, v_v_1043_);
lean_ctor_set(v___x_1036_, 1, v_k_1042_);
lean_ctor_set(v___x_1036_, 0, v___x_1087_);
v___x_1089_ = v___x_1036_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_l_1062_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_nat_add(v___x_1070_, v_size_1040_);
if (lean_obj_tag(v_r_1063_) == 0)
{
lean_object* v_size_1091_; 
v_size_1091_ = lean_ctor_get(v_r_1063_, 0);
lean_inc(v_size_1091_);
v___y_1074_ = v___x_1090_;
v___y_1075_ = v___x_1089_;
v___y_1076_ = v_size_1091_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___y_1074_ = v___x_1090_;
v___y_1075_ = v___x_1089_;
v___y_1076_ = v___x_1092_;
goto v___jp_1073_;
}
}
}
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_del_object(v___x_1036_);
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_add(v___x_1102_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1104_ = lean_nat_add(v___x_1103_, v_size_1040_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_nat_add(v___x_1102_, v_size_1040_);
v___x_1106_ = lean_nat_add(v___x_1105_, v_size_1059_);
lean_dec(v___x_1105_);
lean_inc_ref(v_r_1034_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v_r_1034_);
lean_ctor_set(v___x_1056_, 3, v_r_1045_);
lean_ctor_set(v___x_1056_, 2, v_v_1032_);
lean_ctor_set(v___x_1056_, 1, v_k_1031_);
lean_ctor_set(v___x_1056_, 0, v___x_1106_);
v___x_1108_ = v___x_1056_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_r_1045_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_r_1034_);
v___x_1108_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_isSharedCheck_1115_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1116_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_1034_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_r_1034_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1120_);
v___x_1110_ = v_r_1034_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v_r_1034_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 4, v___x_1108_);
lean_ctor_set(v___x_1110_, 3, v_l_1044_);
lean_ctor_set(v___x_1110_, 2, v_v_1043_);
lean_ctor_set(v___x_1110_, 1, v_k_1042_);
lean_ctor_set(v___x_1110_, 0, v___x_1104_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v___x_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref_known(v_l_1044_, 5);
lean_del_object(v___x_1056_);
lean_dec(v_v_1043_);
lean_dec(v_k_1042_);
lean_dec(v_size_1041_);
lean_dec_ref_known(v_r_1034_, 5);
lean_del_object(v___x_1036_);
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
v___x_1122_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
v___x_1123_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1122_);
return v___x_1123_;
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1056_);
lean_dec(v_r_1045_);
lean_dec(v_v_1043_);
lean_dec(v_k_1042_);
lean_dec(v_size_1041_);
lean_dec_ref_known(v_r_1034_, 5);
lean_del_object(v___x_1036_);
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
v___x_1124_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
v___x_1125_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1124_);
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_size_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v_size_1132_ = lean_ctor_get(v_r_1034_, 0);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_add(v___x_1133_, v_size_1132_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1134_);
v___x_1136_ = v___x_1036_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_r_1034_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_l_1138_; 
v_l_1138_ = lean_ctor_get(v___x_1039_, 3);
lean_inc(v_l_1138_);
if (lean_obj_tag(v_l_1138_) == 0)
{
lean_object* v_r_1139_; 
v_r_1139_ = lean_ctor_get(v___x_1039_, 4);
lean_inc(v_r_1139_);
if (lean_obj_tag(v_r_1139_) == 0)
{
lean_object* v_size_1140_; lean_object* v_k_1141_; lean_object* v_v_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1156_; 
v_size_1140_ = lean_ctor_get(v___x_1039_, 0);
v_k_1141_ = lean_ctor_get(v___x_1039_, 1);
v_v_1142_ = lean_ctor_get(v___x_1039_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1157_ = lean_ctor_get(v___x_1039_, 4);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v___x_1039_, 3);
lean_dec(v_unused_1158_);
v___x_1144_ = v___x_1039_;
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_v_1142_);
lean_inc(v_k_1141_);
lean_inc(v_size_1140_);
lean_dec(v___x_1039_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_size_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v_size_1146_ = lean_ctor_get(v_r_1139_, 0);
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_add(v___x_1147_, v_size_1140_);
lean_dec(v_size_1140_);
v___x_1149_ = lean_nat_add(v___x_1147_, v_size_1146_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 4, v_r_1034_);
lean_ctor_set(v___x_1144_, 3, v_r_1139_);
lean_ctor_set(v___x_1144_, 2, v_v_1032_);
lean_ctor_set(v___x_1144_, 1, v_k_1031_);
lean_ctor_set(v___x_1144_, 0, v___x_1149_);
v___x_1151_ = v___x_1144_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_r_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_r_1034_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1151_);
lean_ctor_set(v___x_1036_, 3, v_l_1138_);
lean_ctor_set(v___x_1036_, 2, v_v_1142_);
lean_ctor_set(v___x_1036_, 1, v_k_1141_);
lean_ctor_set(v___x_1036_, 0, v___x_1148_);
v___x_1153_ = v___x_1036_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_k_1159_; lean_object* v_v_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1172_; 
v_k_1159_ = lean_ctor_get(v___x_1039_, 1);
v_v_1160_ = lean_ctor_get(v___x_1039_, 2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1173_ = lean_ctor_get(v___x_1039_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v___x_1039_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1175_);
v___x_1162_ = v___x_1039_;
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_v_1160_);
lean_inc(v_k_1159_);
lean_dec(v___x_1039_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_unsigned_to_nat(3u);
v___x_1165_ = lean_unsigned_to_nat(1u);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 3, v_r_1139_);
lean_ctor_set(v___x_1162_, 2, v_v_1032_);
lean_ctor_set(v___x_1162_, 1, v_k_1031_);
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_r_1139_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_r_1139_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1167_);
lean_ctor_set(v___x_1036_, 3, v_l_1138_);
lean_ctor_set(v___x_1036_, 2, v_v_1160_);
lean_ctor_set(v___x_1036_, 1, v_k_1159_);
lean_ctor_set(v___x_1036_, 0, v___x_1164_);
v___x_1169_ = v___x_1036_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1159_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
else
{
lean_object* v_r_1176_; 
v_r_1176_ = lean_ctor_get(v___x_1039_, 4);
lean_inc(v_r_1176_);
if (lean_obj_tag(v_r_1176_) == 0)
{
lean_object* v_k_1177_; lean_object* v_v_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1202_; 
v_k_1177_ = lean_ctor_get(v___x_1039_, 1);
v_v_1178_ = lean_ctor_get(v___x_1039_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; 
v_unused_1203_ = lean_ctor_get(v___x_1039_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v___x_1039_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1205_);
v___x_1180_ = v___x_1039_;
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_v_1178_);
lean_inc(v_k_1177_);
lean_dec(v___x_1039_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_k_1182_; lean_object* v_v_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1198_; 
v_k_1182_ = lean_ctor_get(v_r_1176_, 1);
v_v_1183_ = lean_ctor_get(v_r_1176_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_r_1176_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1199_ = lean_ctor_get(v_r_1176_, 4);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_r_1176_, 3);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1176_, 0);
lean_dec(v_unused_1201_);
v___x_1185_ = v_r_1176_;
v_isShared_1186_ = v_isSharedCheck_1198_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_v_1183_);
lean_inc(v_k_1182_);
lean_dec(v_r_1176_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1198_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_unsigned_to_nat(3u);
v___x_1188_ = lean_unsigned_to_nat(1u);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 4, v_l_1138_);
lean_ctor_set(v___x_1185_, 3, v_l_1138_);
lean_ctor_set(v___x_1185_, 2, v_v_1178_);
lean_ctor_set(v___x_1185_, 1, v_k_1177_);
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1177_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1178_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_l_1138_);
v___x_1190_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 4, v_l_1138_);
lean_ctor_set(v___x_1180_, 2, v_v_1032_);
lean_ctor_set(v___x_1180_, 1, v_k_1031_);
lean_ctor_set(v___x_1180_, 0, v___x_1188_);
v___x_1192_ = v___x_1180_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_l_1138_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1192_);
lean_ctor_set(v___x_1036_, 3, v___x_1190_);
lean_ctor_set(v___x_1036_, 2, v_v_1183_);
lean_ctor_set(v___x_1036_, 1, v_k_1182_);
lean_ctor_set(v___x_1036_, 0, v___x_1187_);
v___x_1194_ = v___x_1036_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1182_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_unsigned_to_nat(2u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1176_);
lean_ctor_set(v___x_1036_, 3, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1206_);
v___x_1208_ = v___x_1036_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1176_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1039_);
lean_ctor_set(v___x_1036_, 3, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1210_);
v___x_1212_ = v___x_1036_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___x_1039_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
case 1:
{
lean_object* v___x_1215_; 
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 2, v_v_1028_);
lean_ctor_set(v___x_1036_, 1, v_k_1027_);
v___x_1215_ = v___x_1036_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_size_1030_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1027_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1028_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_r_1034_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
default: 
{
lean_object* v___x_1217_; 
lean_dec(v_size_1030_);
v___x_1217_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1027_, v_v_1028_, v_r_1034_);
if (lean_obj_tag(v_l_1033_) == 0)
{
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_size_1218_; lean_object* v_size_1219_; lean_object* v_k_1220_; lean_object* v_v_1221_; lean_object* v_l_1222_; lean_object* v_r_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_size_1218_ = lean_ctor_get(v_l_1033_, 0);
v_size_1219_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_size_1219_);
v_k_1220_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_k_1220_);
v_v_1221_ = lean_ctor_get(v___x_1217_, 2);
lean_inc(v_v_1221_);
v_l_1222_ = lean_ctor_get(v___x_1217_, 3);
lean_inc(v_l_1222_);
v_r_1223_ = lean_ctor_get(v___x_1217_, 4);
lean_inc(v_r_1223_);
v___x_1224_ = lean_unsigned_to_nat(3u);
v___x_1225_ = lean_nat_mul(v___x_1224_, v_size_1218_);
v___x_1226_ = lean_nat_dec_lt(v___x_1225_, v_size_1219_);
lean_dec(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_dec(v_r_1223_);
lean_dec(v_l_1222_);
lean_dec(v_v_1221_);
lean_dec(v_k_1220_);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v___x_1227_, v_size_1218_);
v___x_1229_ = lean_nat_add(v___x_1228_, v_size_1219_);
lean_dec(v_size_1219_);
lean_dec(v___x_1228_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1217_);
lean_ctor_set(v___x_1036_, 0, v___x_1229_);
v___x_1231_ = v___x_1036_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v___x_1217_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1302_; 
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; 
v_unused_1303_ = lean_ctor_get(v___x_1217_, 4);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v___x_1217_, 3);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v___x_1217_, 2);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v___x_1217_, 1);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1307_);
v___x_1234_ = v___x_1217_;
v_isShared_1235_ = v_isSharedCheck_1302_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v___x_1217_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1302_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
if (lean_obj_tag(v_l_1222_) == 0)
{
if (lean_obj_tag(v_r_1223_) == 0)
{
lean_object* v_size_1236_; lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v_l_1239_; lean_object* v_r_1240_; lean_object* v_size_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_size_1236_ = lean_ctor_get(v_l_1222_, 0);
v_k_1237_ = lean_ctor_get(v_l_1222_, 1);
v_v_1238_ = lean_ctor_get(v_l_1222_, 2);
v_l_1239_ = lean_ctor_get(v_l_1222_, 3);
v_r_1240_ = lean_ctor_get(v_l_1222_, 4);
v_size_1241_ = lean_ctor_get(v_r_1223_, 0);
v___x_1242_ = lean_unsigned_to_nat(2u);
v___x_1243_ = lean_nat_mul(v___x_1242_, v_size_1241_);
v___x_1244_ = lean_nat_dec_lt(v_size_1236_, v___x_1243_);
lean_dec(v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1273_; 
lean_inc(v_r_1240_);
lean_inc(v_l_1239_);
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_l_1222_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; lean_object* v_unused_1275_; lean_object* v_unused_1276_; lean_object* v_unused_1277_; lean_object* v_unused_1278_; 
v_unused_1274_ = lean_ctor_get(v_l_1222_, 4);
lean_dec(v_unused_1274_);
v_unused_1275_ = lean_ctor_get(v_l_1222_, 3);
lean_dec(v_unused_1275_);
v_unused_1276_ = lean_ctor_get(v_l_1222_, 2);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v_l_1222_, 1);
lean_dec(v_unused_1277_);
v_unused_1278_ = lean_ctor_get(v_l_1222_, 0);
lean_dec(v_unused_1278_);
v___x_1246_ = v_l_1222_;
v_isShared_1247_ = v_isSharedCheck_1273_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v_l_1222_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1273_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1263_; 
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v___x_1248_, v_size_1218_);
v___x_1250_ = lean_nat_add(v___x_1249_, v_size_1219_);
lean_dec(v_size_1219_);
if (lean_obj_tag(v_l_1239_) == 0)
{
lean_object* v_size_1271_; 
v_size_1271_ = lean_ctor_get(v_l_1239_, 0);
lean_inc(v_size_1271_);
v___y_1263_ = v_size_1271_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v___y_1263_ = v___x_1272_;
goto v___jp_1262_;
}
v___jp_1251_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_nat_add(v___y_1252_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec(v___y_1252_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 4, v_r_1223_);
lean_ctor_set(v___x_1246_, 3, v_r_1240_);
lean_ctor_set(v___x_1246_, 2, v_v_1221_);
lean_ctor_set(v___x_1246_, 1, v_k_1220_);
lean_ctor_set(v___x_1246_, 0, v___x_1255_);
v___x_1257_ = v___x_1246_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1220_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1221_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_r_1240_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1223_);
v___x_1257_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v___x_1257_);
lean_ctor_set(v___x_1234_, 3, v___y_1253_);
lean_ctor_set(v___x_1234_, 2, v_v_1238_);
lean_ctor_set(v___x_1234_, 1, v_k_1237_);
lean_ctor_set(v___x_1234_, 0, v___x_1250_);
v___x_1259_ = v___x_1234_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v___y_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_nat_add(v___x_1249_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec(v___x_1249_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_l_1239_);
lean_ctor_set(v___x_1036_, 0, v___x_1264_);
v___x_1266_ = v___x_1036_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_l_1239_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_nat_add(v___x_1248_, v_size_1241_);
if (lean_obj_tag(v_r_1240_) == 0)
{
lean_object* v_size_1268_; 
v_size_1268_ = lean_ctor_get(v_r_1240_, 0);
lean_inc(v_size_1268_);
v___y_1252_ = v___x_1267_;
v___y_1253_ = v___x_1266_;
v___y_1254_ = v_size_1268_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
v___y_1252_ = v___x_1267_;
v___y_1253_ = v___x_1266_;
v___y_1254_ = v___x_1269_;
goto v___jp_1251_;
}
}
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_del_object(v___x_1036_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v___x_1279_, v_size_1218_);
v___x_1281_ = lean_nat_add(v___x_1280_, v_size_1219_);
lean_dec(v_size_1219_);
v___x_1282_ = lean_nat_add(v___x_1280_, v_size_1236_);
lean_dec(v___x_1280_);
lean_inc_ref(v_l_1033_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v_l_1222_);
lean_ctor_set(v___x_1234_, 3, v_l_1033_);
lean_ctor_set(v___x_1234_, 2, v_v_1032_);
lean_ctor_set(v___x_1234_, 1, v_k_1031_);
lean_ctor_set(v___x_1234_, 0, v___x_1282_);
v___x_1284_ = v___x_1234_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_l_1222_);
v___x_1284_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_isSharedCheck_1291_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; 
v_unused_1292_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1296_);
v___x_1286_ = v_l_1033_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v_l_1033_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 4, v_r_1223_);
lean_ctor_set(v___x_1286_, 3, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v_v_1221_);
lean_ctor_set(v___x_1286_, 1, v_k_1220_);
lean_ctor_set(v___x_1286_, 0, v___x_1281_);
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1220_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1221_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1223_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref_known(v_l_1222_, 5);
lean_del_object(v___x_1234_);
lean_dec(v_v_1221_);
lean_dec(v_k_1220_);
lean_dec(v_size_1219_);
lean_dec_ref_known(v_l_1033_, 5);
lean_del_object(v___x_1036_);
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
v___x_1298_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
v___x_1299_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1298_);
return v___x_1299_;
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_del_object(v___x_1234_);
lean_dec(v_r_1223_);
lean_dec(v_v_1221_);
lean_dec(v_k_1220_);
lean_dec(v_size_1219_);
lean_dec_ref_known(v_l_1033_, 5);
lean_del_object(v___x_1036_);
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
v___x_1300_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
v___x_1301_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1300_);
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_size_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v_size_1308_ = lean_ctor_get(v_l_1033_, 0);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = lean_nat_add(v___x_1309_, v_size_1308_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1217_);
lean_ctor_set(v___x_1036_, 0, v___x_1310_);
v___x_1312_ = v___x_1036_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1217_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_l_1314_; 
v_l_1314_ = lean_ctor_get(v___x_1217_, 3);
lean_inc(v_l_1314_);
if (lean_obj_tag(v_l_1314_) == 0)
{
lean_object* v_r_1315_; 
v_r_1315_ = lean_ctor_get(v___x_1217_, 4);
lean_inc(v_r_1315_);
if (lean_obj_tag(v_r_1315_) == 0)
{
lean_object* v_size_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1332_; 
v_size_1316_ = lean_ctor_get(v___x_1217_, 0);
v_k_1317_ = lean_ctor_get(v___x_1217_, 1);
v_v_1318_ = lean_ctor_get(v___x_1217_, 2);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; lean_object* v_unused_1334_; 
v_unused_1333_ = lean_ctor_get(v___x_1217_, 4);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v___x_1217_, 3);
lean_dec(v_unused_1334_);
v___x_1320_ = v___x_1217_;
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_v_1318_);
lean_inc(v_k_1317_);
lean_inc(v_size_1316_);
lean_dec(v___x_1217_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_size_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_size_1322_ = lean_ctor_get(v_l_1314_, 0);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_add(v___x_1323_, v_size_1316_);
lean_dec(v_size_1316_);
v___x_1325_ = lean_nat_add(v___x_1323_, v_size_1322_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 4, v_l_1314_);
lean_ctor_set(v___x_1320_, 3, v_l_1033_);
lean_ctor_set(v___x_1320_, 2, v_v_1032_);
lean_ctor_set(v___x_1320_, 1, v_k_1031_);
lean_ctor_set(v___x_1320_, 0, v___x_1325_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_l_1314_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1315_);
lean_ctor_set(v___x_1036_, 3, v___x_1327_);
lean_ctor_set(v___x_1036_, 2, v_v_1318_);
lean_ctor_set(v___x_1036_, 1, v_k_1317_);
lean_ctor_set(v___x_1036_, 0, v___x_1324_);
v___x_1329_ = v___x_1036_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1317_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_r_1315_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1360_; 
v_k_1335_ = lean_ctor_get(v___x_1217_, 1);
v_v_1336_ = lean_ctor_get(v___x_1217_, 2);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1361_ = lean_ctor_get(v___x_1217_, 4);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v___x_1217_, 3);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1363_);
v___x_1338_ = v___x_1217_;
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_v_1336_);
lean_inc(v_k_1335_);
lean_dec(v___x_1217_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_k_1340_; lean_object* v_v_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_k_1340_ = lean_ctor_get(v_l_1314_, 1);
v_v_1341_ = lean_ctor_get(v_l_1314_, 2);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_l_1314_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1357_ = lean_ctor_get(v_l_1314_, 4);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_l_1314_, 3);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_l_1314_, 0);
lean_dec(v_unused_1359_);
v___x_1343_ = v_l_1314_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_v_1341_);
lean_inc(v_k_1340_);
lean_dec(v_l_1314_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1345_ = lean_unsigned_to_nat(3u);
v___x_1346_ = lean_unsigned_to_nat(1u);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_r_1315_);
lean_ctor_set(v___x_1343_, 3, v_r_1315_);
lean_ctor_set(v___x_1343_, 2, v_v_1032_);
lean_ctor_set(v___x_1343_, 1, v_k_1031_);
lean_ctor_set(v___x_1343_, 0, v___x_1346_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_r_1315_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_r_1315_);
v___x_1348_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 3, v_r_1315_);
lean_ctor_set(v___x_1338_, 0, v___x_1346_);
v___x_1350_ = v___x_1338_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_k_1335_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_v_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_r_1315_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_r_1315_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1350_);
lean_ctor_set(v___x_1036_, 3, v___x_1348_);
lean_ctor_set(v___x_1036_, 2, v_v_1341_);
lean_ctor_set(v___x_1036_, 1, v_k_1340_);
lean_ctor_set(v___x_1036_, 0, v___x_1345_);
v___x_1352_ = v___x_1036_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_k_1340_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_v_1341_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1364_; 
v_r_1364_ = lean_ctor_get(v___x_1217_, 4);
lean_inc(v_r_1364_);
if (lean_obj_tag(v_r_1364_) == 0)
{
lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1378_; 
v_k_1365_ = lean_ctor_get(v___x_1217_, 1);
v_v_1366_ = lean_ctor_get(v___x_1217_, 2);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; 
v_unused_1379_ = lean_ctor_get(v___x_1217_, 4);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v___x_1217_, 3);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1381_);
v___x_1368_ = v___x_1217_;
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_v_1366_);
lean_inc(v_k_1365_);
lean_dec(v___x_1217_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_unsigned_to_nat(3u);
v___x_1371_ = lean_unsigned_to_nat(1u);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_l_1314_);
lean_ctor_set(v___x_1368_, 2, v_v_1032_);
lean_ctor_set(v___x_1368_, 1, v_k_1031_);
lean_ctor_set(v___x_1368_, 0, v___x_1371_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_l_1314_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_l_1314_);
v___x_1373_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1364_);
lean_ctor_set(v___x_1036_, 3, v___x_1373_);
lean_ctor_set(v___x_1036_, 2, v_v_1366_);
lean_ctor_set(v___x_1036_, 1, v_k_1365_);
lean_ctor_set(v___x_1036_, 0, v___x_1370_);
v___x_1375_ = v___x_1036_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_r_1364_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_unsigned_to_nat(2u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1217_);
lean_ctor_set(v___x_1036_, 3, v_r_1364_);
lean_ctor_set(v___x_1036_, 0, v___x_1382_);
v___x_1384_ = v___x_1036_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_r_1364_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v___x_1217_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1217_);
lean_ctor_set(v___x_1036_, 3, v___x_1217_);
lean_ctor_set(v___x_1036_, 0, v___x_1386_);
v___x_1388_ = v___x_1036_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___x_1217_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v_k_1027_);
lean_ctor_set(v___x_1392_, 2, v_v_1028_);
lean_ctor_set(v___x_1392_, 3, v_t_1029_);
lean_ctor_set(v___x_1392_, 4, v_t_1029_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* v_init_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v_l_1397_; lean_object* v_r_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_k_1395_ = lean_ctor_get(v_x_1394_, 1);
lean_inc(v_k_1395_);
v_v_1396_ = lean_ctor_get(v_x_1394_, 2);
lean_inc(v_v_1396_);
v_l_1397_ = lean_ctor_get(v_x_1394_, 3);
lean_inc(v_l_1397_);
v_r_1398_ = lean_ctor_get(v_x_1394_, 4);
lean_inc(v_r_1398_);
lean_dec_ref_known(v_x_1394_, 5);
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1393_, v_l_1397_);
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Name_toString(v_k_1395_, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_v_1396_);
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v___x_1401_, v___x_1402_, v___x_1399_);
v_init_1393_ = v___x_1403_;
v_x_1394_ = v_r_1398_;
goto _start;
}
else
{
return v_init_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* v_m_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(1);
v___x_1407_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v___x_1406_, v_m_1405_);
v___x_1408_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* v_env_1414_){
_start:
{
lean_object* v_lake_1415_; lean_object* v_lean_1416_; lean_object* v_elan_x3f_1417_; lean_object* v_pkgUrlMap_1418_; uint8_t v_noCache_1419_; lean_object* v_lakeConfig_x3f_1420_; lean_object* v_cacheKey_x3f_1421_; lean_object* v_cacheArtifactEndpoint_x3f_1422_; lean_object* v_cacheRevisionEndpoint_x3f_1423_; lean_object* v_cacheService_x3f_1424_; lean_object* v_toolchain_1425_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___x_1554_; lean_object* v___y_1556_; 
v_lake_1415_ = lean_ctor_get(v_env_1414_, 0);
lean_inc_ref(v_lake_1415_);
v_lean_1416_ = lean_ctor_get(v_env_1414_, 1);
lean_inc_ref(v_lean_1416_);
v_elan_x3f_1417_ = lean_ctor_get(v_env_1414_, 2);
lean_inc(v_elan_x3f_1417_);
v_pkgUrlMap_1418_ = lean_ctor_get(v_env_1414_, 5);
lean_inc(v_pkgUrlMap_1418_);
v_noCache_1419_ = lean_ctor_get_uint8(v_env_1414_, sizeof(void*)*20);
v_lakeConfig_x3f_1420_ = lean_ctor_get(v_env_1414_, 10);
lean_inc(v_lakeConfig_x3f_1420_);
v_cacheKey_x3f_1421_ = lean_ctor_get(v_env_1414_, 11);
lean_inc(v_cacheKey_x3f_1421_);
v_cacheArtifactEndpoint_x3f_1422_ = lean_ctor_get(v_env_1414_, 12);
lean_inc(v_cacheArtifactEndpoint_x3f_1422_);
v_cacheRevisionEndpoint_x3f_1423_ = lean_ctor_get(v_env_1414_, 13);
lean_inc(v_cacheRevisionEndpoint_x3f_1423_);
v_cacheService_x3f_1424_ = lean_ctor_get(v_env_1414_, 14);
lean_inc(v_cacheService_x3f_1424_);
v_toolchain_1425_ = lean_ctor_get(v_env_1414_, 19);
lean_inc_ref(v_toolchain_1425_);
lean_dec_ref(v_env_1414_);
v___x_1554_ = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
if (lean_obj_tag(v_elan_x3f_1417_) == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_box(0);
v___y_1556_ = v___x_1569_;
goto v___jp_1555_;
}
else
{
lean_object* v_val_1570_; lean_object* v_elan_1571_; lean_object* v___x_1572_; 
v_val_1570_ = lean_ctor_get(v_elan_x3f_1417_, 0);
v_elan_1571_ = lean_ctor_get(v_val_1570_, 1);
lean_inc_ref(v_elan_1571_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_elan_1571_);
v___y_1556_ = v___x_1572_;
goto v___jp_1555_;
}
v___jp_1426_:
{
lean_object* v_sysroot_1440_; lean_object* v_lean_1441_; lean_object* v_ar_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_sysroot_1440_ = lean_ctor_get(v_lean_1416_, 0);
v_lean_1441_ = lean_ctor_get(v_lean_1416_, 7);
v_ar_1442_ = lean_ctor_get(v_lean_1416_, 13);
lean_inc_ref(v___y_1428_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1428_);
lean_ctor_set(v___x_1443_, 1, v___y_1439_);
v___x_1444_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(v_lean_1441_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_lean_1441_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(v_sysroot_1440_);
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_sysroot_1440_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(v_ar_1442_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_ar_1442_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
v___x_1454_ = l_Lake_LeanInstall_leanCc_x3f(v_lean_1416_);
lean_dec_ref(v_lean_1416_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(16u);
v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1458_ = lean_array_push(v___x_1457_, v___y_1436_);
v___x_1459_ = lean_array_push(v___x_1458_, v___y_1432_);
v___x_1460_ = lean_array_push(v___x_1459_, v___y_1427_);
v___x_1461_ = lean_array_push(v___x_1460_, v___y_1438_);
v___x_1462_ = lean_array_push(v___x_1461_, v___y_1433_);
v___x_1463_ = lean_array_push(v___x_1462_, v___y_1435_);
v___x_1464_ = lean_array_push(v___x_1463_, v___y_1434_);
v___x_1465_ = lean_array_push(v___x_1464_, v___y_1431_);
v___x_1466_ = lean_array_push(v___x_1465_, v___y_1430_);
v___x_1467_ = lean_array_push(v___x_1466_, v___y_1437_);
v___x_1468_ = lean_array_push(v___x_1467_, v___y_1429_);
v___x_1469_ = lean_array_push(v___x_1468_, v___x_1443_);
v___x_1470_ = lean_array_push(v___x_1469_, v___x_1446_);
v___x_1471_ = lean_array_push(v___x_1470_, v___x_1449_);
v___x_1472_ = lean_array_push(v___x_1471_, v___x_1452_);
v___x_1473_ = lean_array_push(v___x_1472_, v___x_1455_);
return v___x_1473_;
}
v___jp_1474_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc_ref(v___y_1483_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1483_);
lean_inc_ref(v___y_1480_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1480_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v_cacheKey_x3f_1421_);
v___x_1488_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v_cacheArtifactEndpoint_x3f_1422_);
v___x_1490_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_cacheRevisionEndpoint_x3f_1423_);
v___x_1492_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
if (lean_obj_tag(v_cacheService_x3f_1424_) == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_box(0);
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___x_1492_;
v___y_1429_ = v___x_1491_;
v___y_1430_ = v___x_1487_;
v___y_1431_ = v___x_1485_;
v___y_1432_ = v___y_1476_;
v___y_1433_ = v___y_1477_;
v___y_1434_ = v___y_1478_;
v___y_1435_ = v___y_1479_;
v___y_1436_ = v___y_1481_;
v___y_1437_ = v___x_1489_;
v___y_1438_ = v___y_1482_;
v___y_1439_ = v___x_1493_;
goto v___jp_1426_;
}
else
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_val_1494_ = lean_ctor_get(v_cacheService_x3f_1424_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_cacheService_x3f_1424_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v_cacheService_x3f_1424_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v_cacheService_x3f_1424_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_val_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___x_1492_;
v___y_1429_ = v___x_1491_;
v___y_1430_ = v___x_1487_;
v___y_1431_ = v___x_1485_;
v___y_1432_ = v___y_1476_;
v___y_1433_ = v___y_1477_;
v___y_1434_ = v___y_1478_;
v___y_1435_ = v___y_1479_;
v___y_1436_ = v___y_1481_;
v___y_1437_ = v___x_1489_;
v___y_1438_ = v___y_1482_;
v___y_1439_ = v___x_1499_;
goto v___jp_1426_;
}
}
}
}
v___jp_1502_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v___y_1506_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1506_);
lean_ctor_set(v___x_1510_, 1, v___y_1509_);
v___x_1511_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_1512_ = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(v_pkgUrlMap_1418_);
v___x_1513_ = l_Lean_Json_compress(v___x_1512_);
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1511_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
if (v_noCache_1419_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = ((lean_object*)(l_Lake_Env_baseVars___closed__1));
v___y_1475_ = v___y_1503_;
v___y_1476_ = v___y_1504_;
v___y_1477_ = v___y_1505_;
v___y_1478_ = v___x_1515_;
v___y_1479_ = v___x_1510_;
v___y_1480_ = v___x_1516_;
v___y_1481_ = v___y_1507_;
v___y_1482_ = v___y_1508_;
v___y_1483_ = v___x_1517_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1518_; 
v___x_1518_ = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
v___y_1475_ = v___y_1503_;
v___y_1476_ = v___y_1504_;
v___y_1477_ = v___y_1505_;
v___y_1478_ = v___x_1515_;
v___y_1479_ = v___x_1510_;
v___y_1480_ = v___x_1516_;
v___y_1481_ = v___y_1507_;
v___y_1482_ = v___y_1508_;
v___y_1483_ = v___x_1518_;
goto v___jp_1474_;
}
}
v___jp_1519_:
{
lean_object* v_home_1524_; lean_object* v_lake_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_home_1524_ = lean_ctor_get(v_lake_1415_, 0);
lean_inc_ref(v_home_1524_);
v_lake_1525_ = lean_ctor_get(v_lake_1415_, 5);
lean_inc_ref(v_lake_1525_);
lean_dec_ref(v_lake_1415_);
lean_inc_ref(v___y_1521_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___y_1521_);
lean_ctor_set(v___x_1526_, 1, v___y_1523_);
v___x_1527_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_lake_1525_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_home_1524_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
if (lean_obj_tag(v_lakeConfig_x3f_1420_) == 1)
{
lean_object* v_val_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_val_1534_ = lean_ctor_get(v_lakeConfig_x3f_1420_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_lakeConfig_x3f_1420_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v_lakeConfig_x3f_1420_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_val_1534_);
lean_dec(v_lakeConfig_x3f_1420_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_val_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v___y_1503_ = v___x_1526_;
v___y_1504_ = v___y_1520_;
v___y_1505_ = v___x_1532_;
v___y_1506_ = v___x_1533_;
v___y_1507_ = v___y_1522_;
v___y_1508_ = v___x_1529_;
v___y_1509_ = v___x_1539_;
goto v___jp_1502_;
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_lakeConfig_x3f_1420_);
v___x_1542_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1503_ = v___x_1526_;
v___y_1504_ = v___y_1520_;
v___y_1505_ = v___x_1532_;
v___y_1506_ = v___x_1533_;
v___y_1507_ = v___y_1522_;
v___y_1508_ = v___x_1529_;
v___y_1509_ = v___x_1542_;
goto v___jp_1502_;
}
}
v___jp_1543_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
lean_inc_ref(v___y_1544_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___y_1544_);
lean_ctor_set(v___x_1547_, 1, v___y_1546_);
v___x_1548_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_1549_ = lean_string_utf8_byte_size(v_toolchain_1425_);
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = lean_nat_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_toolchain_1425_);
v___y_1520_ = v___x_1547_;
v___y_1521_ = v___x_1548_;
v___y_1522_ = v___y_1545_;
v___y_1523_ = v___x_1552_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1553_; 
lean_dec_ref(v_toolchain_1425_);
v___x_1553_ = lean_box(0);
v___y_1520_ = v___x_1547_;
v___y_1521_ = v___x_1548_;
v___y_1522_ = v___y_1545_;
v___y_1523_ = v___x_1553_;
goto v___jp_1519_;
}
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1554_);
lean_ctor_set(v___x_1557_, 1, v___y_1556_);
v___x_1558_ = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(v_elan_x3f_1417_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_box(0);
v___y_1544_ = v___x_1558_;
v___y_1545_ = v___x_1557_;
v___y_1546_ = v___x_1559_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_val_1560_ = lean_ctor_get(v_elan_x3f_1417_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_elan_x3f_1417_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1562_ = v_elan_x3f_1417_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v_elan_x3f_1417_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_home_1564_; lean_object* v___x_1566_; 
v_home_1564_ = lean_ctor_get(v_val_1560_, 0);
lean_inc_ref(v_home_1564_);
lean_dec(v_val_1560_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_home_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_home_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v___y_1544_ = v___x_1558_;
v___y_1545_ = v___x_1557_;
v___y_1546_ = v___x_1566_;
goto v___jp_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1573_, lean_object* v_msg_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v_msg_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* v_00_u03b2_1576_, lean_object* v_k_1577_, lean_object* v_v_1578_, lean_object* v_t_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1577_, v_v_1578_, v_t_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* v_init_1581_, lean_object* v_t_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1581_, v_t_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0(lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0___boxed(lean_object* v_x_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lake_Env_vars___lam__0(v_x_1586_);
lean_dec(v_x_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1(uint8_t v_b_1592_){
_start:
{
if (v_b_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__0));
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__1));
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1___boxed(lean_object* v_b_1595_){
_start:
{
uint8_t v_b_boxed_1596_; lean_object* v_res_1597_; 
v_b_boxed_1596_ = lean_unbox(v_b_1595_);
v_res_1597_ = l_Lake_Env_vars___lam__1(v_b_boxed_1596_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* v_env_1598_){
_start:
{
lean_object* v_enableArtifactCache_x3f_1599_; lean_object* v_restoreAllArtifacts_x3f_1600_; lean_object* v_lakeCache_x3f_1601_; lean_object* v___x_1602_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___x_1655_; lean_object* v___y_1657_; 
v_enableArtifactCache_x3f_1599_ = lean_ctor_get(v_env_1598_, 6);
v_restoreAllArtifacts_x3f_1600_ = lean_ctor_get(v_env_1598_, 7);
v_lakeCache_x3f_1601_ = lean_ctor_get(v_env_1598_, 8);
lean_inc(v_lakeCache_x3f_1601_);
lean_inc_ref(v_env_1598_);
v___x_1602_ = l_Lake_Env_baseVars(v_env_1598_);
v___x_1655_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(v_lakeCache_x3f_1601_) == 1)
{
lean_object* v_val_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_val_1664_ = lean_ctor_get(v_lakeCache_x3f_1601_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_lakeCache_x3f_1601_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v_lakeCache_x3f_1601_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_val_1664_);
lean_dec(v_lakeCache_x3f_1601_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_val_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
v___y_1657_ = v___x_1669_;
goto v___jp_1656_;
}
}
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_lakeCache_x3f_1601_);
v___x_1672_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1657_ = v___x_1672_;
goto v___jp_1656_;
}
v___jp_1603_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_vars_1637_; uint8_t v___x_1638_; 
lean_inc_ref(v___y_1605_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___y_1605_);
lean_ctor_set(v___x_1608_, 1, v___y_1607_);
v___x_1609_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_1610_ = l_Lake_Env_leanPath(v_env_1598_);
v___x_1611_ = l_System_SearchPath_toString(v___x_1610_);
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1609_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_1615_ = l_Lake_Env_leanSrcPath(v_env_1598_);
v___x_1616_ = l_System_SearchPath_toString(v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_1620_ = l_Lake_Env_leanGithash(v_env_1598_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_1624_ = l_Lake_Env_path(v_env_1598_);
v___x_1625_ = l_System_SearchPath_toString(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1623_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_unsigned_to_nat(7u);
v___x_1629_ = lean_mk_empty_array_with_capacity(v___x_1628_);
v___x_1630_ = lean_array_push(v___x_1629_, v___y_1606_);
v___x_1631_ = lean_array_push(v___x_1630_, v___y_1604_);
v___x_1632_ = lean_array_push(v___x_1631_, v___x_1608_);
v___x_1633_ = lean_array_push(v___x_1632_, v___x_1613_);
v___x_1634_ = lean_array_push(v___x_1633_, v___x_1618_);
v___x_1635_ = lean_array_push(v___x_1634_, v___x_1622_);
v___x_1636_ = lean_array_push(v___x_1635_, v___x_1627_);
v_vars_1637_ = l_Array_append___redArg(v___x_1602_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = l_System_Platform_isWindows;
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1639_ = l_Lake_sharedLibPathEnvVar;
v___x_1640_ = l_Lake_Env_sharedLibPath(v_env_1598_);
v___x_1641_ = l_System_SearchPath_toString(v___x_1640_);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1639_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_array_push(v_vars_1637_, v___x_1643_);
return v___x_1644_;
}
else
{
lean_dec_ref(v_env_1598_);
return v_vars_1637_;
}
}
v___jp_1645_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v___y_1646_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___y_1646_);
lean_ctor_set(v___x_1649_, 1, v___y_1648_);
v___x_1650_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1600_) == 1)
{
lean_object* v_val_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v_val_1651_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1600_, 0);
v___x_1652_ = lean_unbox(v_val_1651_);
v___x_1653_ = l_Lake_Env_vars___lam__1(v___x_1652_);
v___y_1604_ = v___x_1649_;
v___y_1605_ = v___x_1650_;
v___y_1606_ = v___y_1647_;
v___y_1607_ = v___x_1653_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lake_Env_vars___lam__0(v_restoreAllArtifacts_x3f_1600_);
v___y_1604_ = v___x_1649_;
v___y_1605_ = v___x_1650_;
v___y_1606_ = v___y_1647_;
v___y_1607_ = v___x_1654_;
goto v___jp_1603_;
}
}
v___jp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1655_);
lean_ctor_set(v___x_1658_, 1, v___y_1657_);
v___x_1659_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (lean_obj_tag(v_enableArtifactCache_x3f_1599_) == 1)
{
lean_object* v_val_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; 
v_val_1660_ = lean_ctor_get(v_enableArtifactCache_x3f_1599_, 0);
v___x_1661_ = lean_unbox(v_val_1660_);
v___x_1662_ = l_Lake_Env_vars___lam__1(v___x_1661_);
v___y_1646_ = v___x_1659_;
v___y_1647_ = v___x_1658_;
v___y_1648_ = v___x_1662_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lake_Env_vars___lam__0(v_enableArtifactCache_x3f_1599_);
v___y_1646_ = v___x_1659_;
v___y_1647_ = v___x_1658_;
v___y_1648_ = v___x_1663_;
goto v___jp_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* v_env_1673_){
_start:
{
lean_object* v_lake_1674_; lean_object* v_lean_1675_; lean_object* v_libDir_1676_; lean_object* v_leanLibDir_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_lake_1674_ = lean_ctor_get(v_env_1673_, 0);
v_lean_1675_ = lean_ctor_get(v_env_1673_, 1);
v_libDir_1676_ = lean_ctor_get(v_lake_1674_, 3);
v_leanLibDir_1677_ = lean_ctor_get(v_lean_1675_, 3);
v___x_1678_ = l_Lake_Env_leanPath(v_env_1673_);
lean_inc_ref(v_leanLibDir_1677_);
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v_leanLibDir_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
lean_inc_ref(v_libDir_1676_);
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_libDir_1676_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* v_env_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lake_Env_leanSearchPath(v_env_1681_);
lean_dec_ref(v_env_1681_);
return v_res_1682_;
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv_default = _init_l_Lake_instInhabitedEnv_default();
lean_mark_persistent(l_Lake_instInhabitedEnv_default);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Env(builtin);
}
#ifdef __cplusplus
}
#endif
