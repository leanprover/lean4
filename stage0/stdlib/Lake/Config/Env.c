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
lean_object* v_val_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_val_168_ = lean_ctor_get(v_elan_x3f_165_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_elan_x3f_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v_elan_x3f_165_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_val_168_);
lean_dec(v_elan_x3f_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_string_utf8_byte_size(v_toolchain_166_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_168_, v_toolchain_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v___x_179_; 
lean_del_object(v___x_170_);
lean_dec(v_val_168_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(lean_object* v_elan_x3f_181_, lean_object* v_toolchain_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(v_elan_x3f_181_, v_toolchain_182_);
lean_dec_ref(v_toolchain_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f(lean_object* v_elan_x3f_184_, lean_object* v_toolchain_185_){
_start:
{
lean_object* v_cache_188_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_197_ = lean_io_getenv(v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_val_204_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_197_, 1);
v___x_205_ = lean_string_utf8_byte_size(v_val_204_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_val_204_);
goto v___jp_198_;
}
else
{
lean_dec(v_elan_x3f_184_);
v_cache_188_ = v_val_204_;
goto v___jp_187_;
}
}
v___jp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_cache_188_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lake_getSystemCacheHome_x3f();
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_val_193_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_191_, 1);
v___x_194_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_195_ = l_System_FilePath_join(v_val_193_, v___x_194_);
v_cache_188_ = v___x_195_;
goto v___jp_187_;
}
}
v___jp_198_:
{
if (lean_obj_tag(v_elan_x3f_184_) == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_val_199_ = lean_ctor_get(v_elan_x3f_184_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v_elan_x3f_184_, 1);
v___x_200_ = lean_string_utf8_byte_size(v_toolchain_185_);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_nat_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_199_, v_toolchain_185_);
v_cache_188_ = v___x_203_;
goto v___jp_187_;
}
else
{
lean_dec(v_val_199_);
goto v___jp_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_computeCache_x3f___boxed(lean_object* v_elan_x3f_208_, lean_object* v_toolchain_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_208_, v_toolchain_209_);
lean_dec_ref(v_toolchain_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(lean_object* v_elan_x3f_212_, lean_object* v_userHome_x3f_213_, lean_object* v_toolchain_214_, lean_object* v_env_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
v___x_218_ = lean_io_getenv(v___x_217_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_userHome_x3f_213_);
lean_dec(v_elan_x3f_212_);
v_val_262_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_331_ == 0)
{
v___x_264_ = v___x_218_;
v_isShared_265_ = v_isSharedCheck_331_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_val_262_);
lean_dec(v___x_218_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_331_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_string_utf8_byte_size(v_val_262_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_nat_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v_lake_269_; lean_object* v_lean_270_; lean_object* v_elan_x3f_271_; lean_object* v_reservoirApiUrl_272_; lean_object* v_githashOverride_273_; lean_object* v_pkgUrlMap_274_; uint8_t v_noCache_275_; lean_object* v_enableArtifactCache_x3f_276_; lean_object* v_restoreAllArtifacts_x3f_277_; uint8_t v_noSystemCache_278_; lean_object* v_lakeConfig_x3f_279_; lean_object* v_cacheKey_x3f_280_; lean_object* v_cacheArtifactEndpoint_x3f_281_; lean_object* v_cacheRevisionEndpoint_x3f_282_; lean_object* v_cacheService_x3f_283_; lean_object* v_initLeanPath_284_; lean_object* v_initLeanSrcPath_285_; lean_object* v_initSharedLibPath_286_; lean_object* v_initPath_287_; lean_object* v_toolchain_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_299_; 
v_lake_269_ = lean_ctor_get(v_env_215_, 0);
v_lean_270_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_271_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_272_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_273_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_274_ = lean_ctor_get(v_env_215_, 5);
v_noCache_275_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20);
v_enableArtifactCache_x3f_276_ = lean_ctor_get(v_env_215_, 6);
v_restoreAllArtifacts_x3f_277_ = lean_ctor_get(v_env_215_, 7);
v_noSystemCache_278_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_279_ = lean_ctor_get(v_env_215_, 10);
v_cacheKey_x3f_280_ = lean_ctor_get(v_env_215_, 11);
v_cacheArtifactEndpoint_x3f_281_ = lean_ctor_get(v_env_215_, 12);
v_cacheRevisionEndpoint_x3f_282_ = lean_ctor_get(v_env_215_, 13);
v_cacheService_x3f_283_ = lean_ctor_get(v_env_215_, 14);
v_initLeanPath_284_ = lean_ctor_get(v_env_215_, 15);
v_initLeanSrcPath_285_ = lean_ctor_get(v_env_215_, 16);
v_initSharedLibPath_286_ = lean_ctor_get(v_env_215_, 17);
v_initPath_287_ = lean_ctor_get(v_env_215_, 18);
v_toolchain_288_ = lean_ctor_get(v_env_215_, 19);
v_isSharedCheck_299_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_300_ = lean_ctor_get(v_env_215_, 9);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_301_);
v___x_290_ = v_env_215_;
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_toolchain_288_);
lean_inc(v_initPath_287_);
lean_inc(v_initSharedLibPath_286_);
lean_inc(v_initLeanSrcPath_285_);
lean_inc(v_initLeanPath_284_);
lean_inc(v_cacheService_x3f_283_);
lean_inc(v_cacheRevisionEndpoint_x3f_282_);
lean_inc(v_cacheArtifactEndpoint_x3f_281_);
lean_inc(v_cacheKey_x3f_280_);
lean_inc(v_lakeConfig_x3f_279_);
lean_inc(v_restoreAllArtifacts_x3f_277_);
lean_inc(v_enableArtifactCache_x3f_276_);
lean_inc(v_pkgUrlMap_274_);
lean_inc(v_githashOverride_273_);
lean_inc(v_reservoirApiUrl_272_);
lean_inc(v_elan_x3f_271_);
lean_inc(v_lean_270_);
lean_inc(v_lake_269_);
lean_dec(v_env_215_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_265_ == 0)
{
v___x_293_ = v___x_264_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_262_);
v___x_293_ = v_reuseFailAlloc_298_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
lean_inc_ref(v___x_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 9, v___x_293_);
lean_ctor_set(v___x_290_, 8, v___x_293_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_lake_269_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_lean_270_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_elan_x3f_271_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_reservoirApiUrl_272_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_githashOverride_273_);
lean_ctor_set(v_reuseFailAlloc_297_, 5, v_pkgUrlMap_274_);
lean_ctor_set(v_reuseFailAlloc_297_, 6, v_enableArtifactCache_x3f_276_);
lean_ctor_set(v_reuseFailAlloc_297_, 7, v_restoreAllArtifacts_x3f_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 8, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 9, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 10, v_lakeConfig_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_297_, 11, v_cacheKey_x3f_280_);
lean_ctor_set(v_reuseFailAlloc_297_, 12, v_cacheArtifactEndpoint_x3f_281_);
lean_ctor_set(v_reuseFailAlloc_297_, 13, v_cacheRevisionEndpoint_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_297_, 14, v_cacheService_x3f_283_);
lean_ctor_set(v_reuseFailAlloc_297_, 15, v_initLeanPath_284_);
lean_ctor_set(v_reuseFailAlloc_297_, 16, v_initLeanSrcPath_285_);
lean_ctor_set(v_reuseFailAlloc_297_, 17, v_initSharedLibPath_286_);
lean_ctor_set(v_reuseFailAlloc_297_, 18, v_initPath_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 19, v_toolchain_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_297_, sizeof(void*)*20, v_noCache_275_);
lean_ctor_set_uint8(v_reuseFailAlloc_297_, sizeof(void*)*20 + 1, v_noSystemCache_278_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
}
else
{
lean_object* v_lake_302_; lean_object* v_lean_303_; lean_object* v_elan_x3f_304_; lean_object* v_reservoirApiUrl_305_; lean_object* v_githashOverride_306_; lean_object* v_pkgUrlMap_307_; uint8_t v_noCache_308_; lean_object* v_enableArtifactCache_x3f_309_; lean_object* v_restoreAllArtifacts_x3f_310_; lean_object* v_lakeCache_x3f_311_; lean_object* v_lakeSystemCache_x3f_312_; lean_object* v_lakeConfig_x3f_313_; lean_object* v_cacheKey_x3f_314_; lean_object* v_cacheArtifactEndpoint_x3f_315_; lean_object* v_cacheRevisionEndpoint_x3f_316_; lean_object* v_cacheService_x3f_317_; lean_object* v_initLeanPath_318_; lean_object* v_initLeanSrcPath_319_; lean_object* v_initSharedLibPath_320_; lean_object* v_initPath_321_; lean_object* v_toolchain_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
lean_del_object(v___x_264_);
lean_dec(v_val_262_);
v_lake_302_ = lean_ctor_get(v_env_215_, 0);
v_lean_303_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_304_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_305_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_306_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_307_ = lean_ctor_get(v_env_215_, 5);
v_noCache_308_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20);
v_enableArtifactCache_x3f_309_ = lean_ctor_get(v_env_215_, 6);
v_restoreAllArtifacts_x3f_310_ = lean_ctor_get(v_env_215_, 7);
v_lakeCache_x3f_311_ = lean_ctor_get(v_env_215_, 8);
v_lakeSystemCache_x3f_312_ = lean_ctor_get(v_env_215_, 9);
v_lakeConfig_x3f_313_ = lean_ctor_get(v_env_215_, 10);
v_cacheKey_x3f_314_ = lean_ctor_get(v_env_215_, 11);
v_cacheArtifactEndpoint_x3f_315_ = lean_ctor_get(v_env_215_, 12);
v_cacheRevisionEndpoint_x3f_316_ = lean_ctor_get(v_env_215_, 13);
v_cacheService_x3f_317_ = lean_ctor_get(v_env_215_, 14);
v_initLeanPath_318_ = lean_ctor_get(v_env_215_, 15);
v_initLeanSrcPath_319_ = lean_ctor_get(v_env_215_, 16);
v_initSharedLibPath_320_ = lean_ctor_get(v_env_215_, 17);
v_initPath_321_ = lean_ctor_get(v_env_215_, 18);
v_toolchain_322_ = lean_ctor_get(v_env_215_, 19);
v_isSharedCheck_330_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v_env_215_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_toolchain_322_);
lean_inc(v_initPath_321_);
lean_inc(v_initSharedLibPath_320_);
lean_inc(v_initLeanSrcPath_319_);
lean_inc(v_initLeanPath_318_);
lean_inc(v_cacheService_x3f_317_);
lean_inc(v_cacheRevisionEndpoint_x3f_316_);
lean_inc(v_cacheArtifactEndpoint_x3f_315_);
lean_inc(v_cacheKey_x3f_314_);
lean_inc(v_lakeConfig_x3f_313_);
lean_inc(v_lakeSystemCache_x3f_312_);
lean_inc(v_lakeCache_x3f_311_);
lean_inc(v_restoreAllArtifacts_x3f_310_);
lean_inc(v_enableArtifactCache_x3f_309_);
lean_inc(v_pkgUrlMap_307_);
lean_inc(v_githashOverride_306_);
lean_inc(v_reservoirApiUrl_305_);
lean_inc(v_elan_x3f_304_);
lean_inc(v_lean_303_);
lean_inc(v_lake_302_);
lean_dec(v_env_215_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_lake_302_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_lean_303_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_elan_x3f_304_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_reservoirApiUrl_305_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v_githashOverride_306_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v_pkgUrlMap_307_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_enableArtifactCache_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 7, v_restoreAllArtifacts_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_329_, 8, v_lakeCache_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_329_, 9, v_lakeSystemCache_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_329_, 10, v_lakeConfig_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_329_, 11, v_cacheKey_x3f_314_);
lean_ctor_set(v_reuseFailAlloc_329_, 12, v_cacheArtifactEndpoint_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_329_, 13, v_cacheRevisionEndpoint_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 14, v_cacheService_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 15, v_initLeanPath_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 16, v_initLeanSrcPath_319_);
lean_ctor_set(v_reuseFailAlloc_329_, 17, v_initSharedLibPath_320_);
lean_ctor_set(v_reuseFailAlloc_329_, 18, v_initPath_321_);
lean_ctor_set(v_reuseFailAlloc_329_, 19, v_toolchain_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_329_, sizeof(void*)*20, v_noCache_308_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; 
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*20 + 1, v___x_268_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
}
}
else
{
lean_dec(v___x_218_);
if (lean_obj_tag(v_elan_x3f_212_) == 0)
{
goto v___jp_219_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_387_; 
v_val_332_ = lean_ctor_get(v_elan_x3f_212_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_elan_x3f_212_);
if (v_isSharedCheck_387_ == 0)
{
v___x_334_ = v_elan_x3f_212_;
v_isShared_335_ = v_isSharedCheck_387_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v_elan_x3f_212_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_387_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_string_utf8_byte_size(v_toolchain_214_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_213_);
v___x_340_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(v_val_332_, v_toolchain_214_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_340_);
v___x_342_ = v___x_334_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_386_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___y_344_; 
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
v___y_344_ = v___x_375_;
goto v___jp_343_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_385_; 
v_val_376_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_385_ == 0)
{
v___x_378_ = v___x_339_;
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_val_376_);
lean_dec(v___x_339_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_381_ = l_System_FilePath_join(v_val_376_, v___x_380_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
v___y_344_ = v___x_383_;
goto v___jp_343_;
}
}
}
v___jp_343_:
{
lean_object* v_lake_345_; lean_object* v_lean_346_; lean_object* v_elan_x3f_347_; lean_object* v_reservoirApiUrl_348_; lean_object* v_githashOverride_349_; lean_object* v_pkgUrlMap_350_; uint8_t v_noCache_351_; lean_object* v_enableArtifactCache_x3f_352_; lean_object* v_restoreAllArtifacts_x3f_353_; uint8_t v_noSystemCache_354_; lean_object* v_lakeConfig_x3f_355_; lean_object* v_cacheKey_x3f_356_; lean_object* v_cacheArtifactEndpoint_x3f_357_; lean_object* v_cacheRevisionEndpoint_x3f_358_; lean_object* v_cacheService_x3f_359_; lean_object* v_initLeanPath_360_; lean_object* v_initLeanSrcPath_361_; lean_object* v_initSharedLibPath_362_; lean_object* v_initPath_363_; lean_object* v_toolchain_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v_lake_345_ = lean_ctor_get(v_env_215_, 0);
v_lean_346_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_347_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_348_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_349_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_350_ = lean_ctor_get(v_env_215_, 5);
v_noCache_351_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20);
v_enableArtifactCache_x3f_352_ = lean_ctor_get(v_env_215_, 6);
v_restoreAllArtifacts_x3f_353_ = lean_ctor_get(v_env_215_, 7);
v_noSystemCache_354_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_355_ = lean_ctor_get(v_env_215_, 10);
v_cacheKey_x3f_356_ = lean_ctor_get(v_env_215_, 11);
v_cacheArtifactEndpoint_x3f_357_ = lean_ctor_get(v_env_215_, 12);
v_cacheRevisionEndpoint_x3f_358_ = lean_ctor_get(v_env_215_, 13);
v_cacheService_x3f_359_ = lean_ctor_get(v_env_215_, 14);
v_initLeanPath_360_ = lean_ctor_get(v_env_215_, 15);
v_initLeanSrcPath_361_ = lean_ctor_get(v_env_215_, 16);
v_initSharedLibPath_362_ = lean_ctor_get(v_env_215_, 17);
v_initPath_363_ = lean_ctor_get(v_env_215_, 18);
v_toolchain_364_ = lean_ctor_get(v_env_215_, 19);
v_isSharedCheck_372_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_env_215_, 9);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_374_);
v___x_366_ = v_env_215_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_toolchain_364_);
lean_inc(v_initPath_363_);
lean_inc(v_initSharedLibPath_362_);
lean_inc(v_initLeanSrcPath_361_);
lean_inc(v_initLeanPath_360_);
lean_inc(v_cacheService_x3f_359_);
lean_inc(v_cacheRevisionEndpoint_x3f_358_);
lean_inc(v_cacheArtifactEndpoint_x3f_357_);
lean_inc(v_cacheKey_x3f_356_);
lean_inc(v_lakeConfig_x3f_355_);
lean_inc(v_restoreAllArtifacts_x3f_353_);
lean_inc(v_enableArtifactCache_x3f_352_);
lean_inc(v_pkgUrlMap_350_);
lean_inc(v_githashOverride_349_);
lean_inc(v_reservoirApiUrl_348_);
lean_inc(v_elan_x3f_347_);
lean_inc(v_lean_346_);
lean_inc(v_lake_345_);
lean_dec(v_env_215_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 9, v___y_344_);
lean_ctor_set(v___x_366_, 8, v___x_342_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_lake_345_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_lean_346_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_elan_x3f_347_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_reservoirApiUrl_348_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_githashOverride_349_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v_pkgUrlMap_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_enableArtifactCache_x3f_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_restoreAllArtifacts_x3f_353_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_371_, 9, v___y_344_);
lean_ctor_set(v_reuseFailAlloc_371_, 10, v_lakeConfig_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_371_, 11, v_cacheKey_x3f_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 12, v_cacheArtifactEndpoint_x3f_357_);
lean_ctor_set(v_reuseFailAlloc_371_, 13, v_cacheRevisionEndpoint_x3f_358_);
lean_ctor_set(v_reuseFailAlloc_371_, 14, v_cacheService_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 15, v_initLeanPath_360_);
lean_ctor_set(v_reuseFailAlloc_371_, 16, v_initLeanSrcPath_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 17, v_initSharedLibPath_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 18, v_initPath_363_);
lean_ctor_set(v_reuseFailAlloc_371_, 19, v_toolchain_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*20, v_noCache_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*20 + 1, v_noSystemCache_354_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
}
}
else
{
lean_del_object(v___x_334_);
lean_dec(v_val_332_);
goto v___jp_219_;
}
}
}
}
v___jp_219_:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_213_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_env_215_);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_261_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_261_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_261_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_261_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_lake_226_; lean_object* v_lean_227_; lean_object* v_elan_x3f_228_; lean_object* v_reservoirApiUrl_229_; lean_object* v_githashOverride_230_; lean_object* v_pkgUrlMap_231_; uint8_t v_noCache_232_; lean_object* v_enableArtifactCache_x3f_233_; lean_object* v_restoreAllArtifacts_x3f_234_; uint8_t v_noSystemCache_235_; lean_object* v_lakeConfig_x3f_236_; lean_object* v_cacheKey_x3f_237_; lean_object* v_cacheArtifactEndpoint_x3f_238_; lean_object* v_cacheRevisionEndpoint_x3f_239_; lean_object* v_cacheService_x3f_240_; lean_object* v_initLeanPath_241_; lean_object* v_initLeanSrcPath_242_; lean_object* v_initSharedLibPath_243_; lean_object* v_initPath_244_; lean_object* v_toolchain_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_258_; 
v_lake_226_ = lean_ctor_get(v_env_215_, 0);
v_lean_227_ = lean_ctor_get(v_env_215_, 1);
v_elan_x3f_228_ = lean_ctor_get(v_env_215_, 2);
v_reservoirApiUrl_229_ = lean_ctor_get(v_env_215_, 3);
v_githashOverride_230_ = lean_ctor_get(v_env_215_, 4);
v_pkgUrlMap_231_ = lean_ctor_get(v_env_215_, 5);
v_noCache_232_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20);
v_enableArtifactCache_x3f_233_ = lean_ctor_get(v_env_215_, 6);
v_restoreAllArtifacts_x3f_234_ = lean_ctor_get(v_env_215_, 7);
v_noSystemCache_235_ = lean_ctor_get_uint8(v_env_215_, sizeof(void*)*20 + 1);
v_lakeConfig_x3f_236_ = lean_ctor_get(v_env_215_, 10);
v_cacheKey_x3f_237_ = lean_ctor_get(v_env_215_, 11);
v_cacheArtifactEndpoint_x3f_238_ = lean_ctor_get(v_env_215_, 12);
v_cacheRevisionEndpoint_x3f_239_ = lean_ctor_get(v_env_215_, 13);
v_cacheService_x3f_240_ = lean_ctor_get(v_env_215_, 14);
v_initLeanPath_241_ = lean_ctor_get(v_env_215_, 15);
v_initLeanSrcPath_242_ = lean_ctor_get(v_env_215_, 16);
v_initSharedLibPath_243_ = lean_ctor_get(v_env_215_, 17);
v_initPath_244_ = lean_ctor_get(v_env_215_, 18);
v_toolchain_245_ = lean_ctor_get(v_env_215_, 19);
v_isSharedCheck_258_ = !lean_is_exclusive(v_env_215_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_259_ = lean_ctor_get(v_env_215_, 9);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_env_215_, 8);
lean_dec(v_unused_260_);
v___x_247_ = v_env_215_;
v_isShared_248_ = v_isSharedCheck_258_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_toolchain_245_);
lean_inc(v_initPath_244_);
lean_inc(v_initSharedLibPath_243_);
lean_inc(v_initLeanSrcPath_242_);
lean_inc(v_initLeanPath_241_);
lean_inc(v_cacheService_x3f_240_);
lean_inc(v_cacheRevisionEndpoint_x3f_239_);
lean_inc(v_cacheArtifactEndpoint_x3f_238_);
lean_inc(v_cacheKey_x3f_237_);
lean_inc(v_lakeConfig_x3f_236_);
lean_inc(v_restoreAllArtifacts_x3f_234_);
lean_inc(v_enableArtifactCache_x3f_233_);
lean_inc(v_pkgUrlMap_231_);
lean_inc(v_githashOverride_230_);
lean_inc(v_reservoirApiUrl_229_);
lean_inc(v_elan_x3f_228_);
lean_inc(v_lean_227_);
lean_inc(v_lake_226_);
lean_dec(v_env_215_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_258_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0));
v___x_250_ = l_System_FilePath_join(v_val_222_, v___x_249_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_250_);
v___x_252_ = v___x_224_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_257_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
lean_inc_ref(v___x_252_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 9, v___x_252_);
lean_ctor_set(v___x_247_, 8, v___x_252_);
v___x_254_ = v___x_247_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_lake_226_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_lean_227_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_elan_x3f_228_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_reservoirApiUrl_229_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_githashOverride_230_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v_pkgUrlMap_231_);
lean_ctor_set(v_reuseFailAlloc_256_, 6, v_enableArtifactCache_x3f_233_);
lean_ctor_set(v_reuseFailAlloc_256_, 7, v_restoreAllArtifacts_x3f_234_);
lean_ctor_set(v_reuseFailAlloc_256_, 8, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 9, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 10, v_lakeConfig_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_256_, 11, v_cacheKey_x3f_237_);
lean_ctor_set(v_reuseFailAlloc_256_, 12, v_cacheArtifactEndpoint_x3f_238_);
lean_ctor_set(v_reuseFailAlloc_256_, 13, v_cacheRevisionEndpoint_x3f_239_);
lean_ctor_set(v_reuseFailAlloc_256_, 14, v_cacheService_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_256_, 15, v_initLeanPath_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 16, v_initLeanSrcPath_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 17, v_initSharedLibPath_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 18, v_initPath_244_);
lean_ctor_set(v_reuseFailAlloc_256_, 19, v_toolchain_245_);
lean_ctor_set_uint8(v_reuseFailAlloc_256_, sizeof(void*)*20, v_noCache_232_);
lean_ctor_set_uint8(v_reuseFailAlloc_256_, sizeof(void*)*20 + 1, v_noSystemCache_235_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(lean_object* v_elan_x3f_388_, lean_object* v_userHome_x3f_389_, lean_object* v_toolchain_390_, lean_object* v_env_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_388_, v_userHome_x3f_389_, v_toolchain_390_, v_env_391_);
lean_dec_ref(v_toolchain_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(lean_object* v_init_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_k_399_; lean_object* v_v_400_; lean_object* v_l_401_; lean_object* v_r_402_; lean_object* v___x_403_; 
v_k_399_ = lean_ctor_get(v_x_398_, 1);
lean_inc(v_k_399_);
v_v_400_ = lean_ctor_get(v_x_398_, 2);
lean_inc(v_v_400_);
v_l_401_ = lean_ctor_get(v_x_398_, 3);
lean_inc(v_l_401_);
v_r_402_ = lean_ctor_get(v_x_398_, 4);
lean_inc(v_r_402_);
lean_dec_ref_known(v_x_398_, 5);
v___x_403_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v_init_397_, v_l_401_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_dec(v_r_402_);
lean_dec(v_v_400_);
lean_dec(v_k_399_);
return v___x_403_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_444_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_444_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0));
v___x_409_ = lean_string_dec_eq(v_k_399_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v_n_410_; uint8_t v___x_411_; 
lean_inc(v_k_399_);
v_n_410_ = l_String_toName(v_k_399_);
v___x_411_ = l_Lean_Name_isAnonymous(v_n_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_del_object(v___x_406_);
lean_dec(v_k_399_);
v___x_412_ = l_Lean_Json_getStr_x3f(v_v_400_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_n_410_);
lean_dec(v_a_404_);
lean_dec(v_r_402_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_412_, 1);
v___x_422_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_410_, v_a_421_, v_a_404_);
v_init_397_ = v___x_422_;
v_x_398_ = v_r_402_;
goto _start;
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
lean_dec(v_n_410_);
lean_dec(v_a_404_);
lean_dec(v_r_402_);
lean_dec(v_v_400_);
v___x_424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1));
v___x_425_ = lean_string_append(v___x_424_, v_k_399_);
lean_dec(v_k_399_);
v___x_426_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v___x_427_);
v___x_429_ = v___x_406_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v___x_431_; 
lean_del_object(v___x_406_);
lean_dec(v_k_399_);
v___x_431_ = l_Lean_Json_getStr_x3f(v_v_400_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_a_404_);
lean_dec(v_r_402_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_431_, 1);
v___x_441_ = lean_box(0);
v___x_442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_441_, v_a_440_, v_a_404_);
v_init_397_ = v___x_442_;
v_x_398_ = v_r_402_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_init_397_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 5)
{
lean_object* v_kvPairs_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_kvPairs_448_ = lean_ctor_get(v_x_447_, 0);
lean_inc(v_kvPairs_448_);
lean_dec_ref_known(v_x_447_, 1);
v___x_449_ = lean_box(1);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v___x_449_, v_kvPairs_448_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_451_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0));
v___x_452_ = lean_unsigned_to_nat(80u);
v___x_453_ = l_Lean_Json_pretty(v_x_447_, v___x_452_);
v___x_454_ = lean_string_append(v___x_451_, v___x_453_);
lean_dec_ref(v___x_453_);
v___x_455_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2));
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap(){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_a_464_; 
v___x_461_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_462_ = lean_io_getenv(v___x_461_);
if (lean_obj_tag(v___x_462_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; 
v_val_468_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_462_, 1);
v___x_469_ = l_Lean_Json_parse(v_val_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v_a_464_ = v_a_470_;
goto v___jp_463_;
}
else
{
lean_object* v_a_471_; lean_object* v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_469_, 1);
v___x_472_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(v_a_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v_a_464_ = v_a_473_;
goto v___jp_463_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 0);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_462_);
v___x_482_ = lean_box(1);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1));
v___x_466_ = lean_string_append(v___x_465_, v_a_464_);
lean_dec_ref(v_a_464_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(lean_object* v_url_486_){
_start:
{
uint32_t v___y_488_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_string_utf8_byte_size(v_url_486_);
lean_inc_ref(v_url_486_);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v_url_486_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
v___x_500_ = l_String_Slice_Pos_prev_x3f(v___x_499_, v___x_498_);
if (lean_obj_tag(v___x_500_) == 0)
{
uint32_t v___x_501_; 
lean_dec_ref_known(v___x_499_, 3);
v___x_501_ = 65;
v___y_488_ = v___x_501_;
goto v___jp_487_;
}
else
{
lean_object* v_val_502_; lean_object* v___x_503_; 
v_val_502_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_val_502_);
lean_dec_ref_known(v___x_500_, 1);
v___x_503_ = l_String_Slice_Pos_get_x3f(v___x_499_, v_val_502_);
lean_dec(v_val_502_);
lean_dec_ref_known(v___x_499_, 3);
if (lean_obj_tag(v___x_503_) == 0)
{
uint32_t v___x_504_; 
v___x_504_ = 65;
v___y_488_ = v___x_504_;
goto v___jp_487_;
}
else
{
lean_object* v_val_505_; uint32_t v___x_506_; 
v_val_505_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___x_503_, 1);
v___x_506_ = lean_unbox_uint32(v_val_505_);
lean_dec(v_val_505_);
v___y_488_ = v___x_506_;
goto v___jp_487_;
}
}
v___jp_487_:
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 47;
v___x_490_ = lean_uint32_dec_eq(v___y_488_, v___x_489_);
if (v___x_490_ == 0)
{
return v_url_486_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_string_utf8_byte_size(v_url_486_);
lean_inc_ref(v_url_486_);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v_url_486_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
v___x_495_ = l_String_Slice_Pos_prevn(v___x_494_, v___x_493_, v___x_491_);
lean_dec_ref_known(v___x_494_, 3);
v___x_496_ = lean_string_utf8_extract(v_url_486_, v___x_492_, v___x_495_);
lean_dec(v___x_495_);
lean_dec_ref(v_url_486_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* v_lake_525_, lean_object* v_lean_526_, lean_object* v_elan_x3f_527_, lean_object* v_noCache_528_){
_start:
{
lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; uint8_t v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; uint8_t v___y_556_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; uint8_t v___y_593_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_val_702_; lean_object* v___y_705_; lean_object* v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v_a_818_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_a_850_; 
v___x_847_ = ((lean_object*)(l_Lake_Env_compute___closed__14));
v___x_848_ = lean_io_getenv(v___x_847_);
if (lean_obj_tag(v___x_848_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_870_; 
v_val_869_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_848_, 1);
v___x_870_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_869_);
v_a_850_ = v___x_870_;
goto v___jp_849_;
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_848_);
v___x_871_ = ((lean_object*)(l_Lake_Env_compute___closed__17));
v_a_850_ = v___x_871_;
goto v___jp_849_;
}
v___jp_530_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_inc_ref(v___y_538_);
lean_inc_n(v___y_531_, 2);
lean_inc(v_elan_x3f_527_);
v___x_550_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v___x_550_, 0, v_lake_525_);
lean_ctor_set(v___x_550_, 1, v_lean_526_);
lean_ctor_set(v___x_550_, 2, v_elan_x3f_527_);
lean_ctor_set(v___x_550_, 3, v___y_532_);
lean_ctor_set(v___x_550_, 4, v___y_537_);
lean_ctor_set(v___x_550_, 5, v___y_543_);
lean_ctor_set(v___x_550_, 6, v___y_546_);
lean_ctor_set(v___x_550_, 7, v___y_545_);
lean_ctor_set(v___x_550_, 8, v___y_531_);
lean_ctor_set(v___x_550_, 9, v___y_531_);
lean_ctor_set(v___x_550_, 10, v___y_533_);
lean_ctor_set(v___x_550_, 11, v___y_536_);
lean_ctor_set(v___x_550_, 12, v___y_547_);
lean_ctor_set(v___x_550_, 13, v___y_544_);
lean_ctor_set(v___x_550_, 14, v___y_549_);
lean_ctor_set(v___x_550_, 15, v___y_548_);
lean_ctor_set(v___x_550_, 16, v___y_539_);
lean_ctor_set(v___x_550_, 17, v___y_542_);
lean_ctor_set(v___x_550_, 18, v___y_540_);
lean_ctor_set(v___x_550_, 19, v___y_538_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*20, v___y_535_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*20 + 1, v___y_534_);
v___x_551_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(v_elan_x3f_527_, v___y_541_, v___y_538_, v___x_550_);
lean_dec_ref(v___y_538_);
return v___x_551_;
}
v___jp_552_:
{
if (lean_obj_tag(v___y_564_) == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
v___y_531_ = v___y_553_;
v___y_532_ = v___y_554_;
v___y_533_ = v___y_555_;
v___y_534_ = v___y_556_;
v___y_535_ = v___y_557_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_559_;
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_566_;
v___y_543_ = v___y_565_;
v___y_544_ = v___y_571_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___x_572_;
goto v___jp_530_;
}
else
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_588_; 
v_val_573_ = lean_ctor_get(v___y_564_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___y_564_);
if (v_isSharedCheck_588_ == 0)
{
v___x_575_ = v___y_564_;
v_isShared_576_ = v_isSharedCheck_588_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v___y_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_588_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_str_581_; lean_object* v_startInclusive_582_; lean_object* v_endExclusive_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_string_utf8_byte_size(v_val_573_);
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v_val_573_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
v___x_580_ = l_String_Slice_trimAscii(v___x_579_);
v_str_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_ref(v_str_581_);
v_startInclusive_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_startInclusive_582_);
v_endExclusive_583_ = lean_ctor_get(v___x_580_, 2);
lean_inc(v_endExclusive_583_);
lean_dec_ref(v___x_580_);
v___x_584_ = lean_string_utf8_extract(v_str_581_, v_startInclusive_582_, v_endExclusive_583_);
lean_dec(v_endExclusive_583_);
lean_dec(v_startInclusive_582_);
lean_dec_ref(v_str_581_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_584_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_531_ = v___y_553_;
v___y_532_ = v___y_554_;
v___y_533_ = v___y_555_;
v___y_534_ = v___y_556_;
v___y_535_ = v___y_557_;
v___y_536_ = v___y_558_;
v___y_537_ = v___y_559_;
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v___y_563_;
v___y_542_ = v___y_566_;
v___y_543_ = v___y_565_;
v___y_544_ = v___y_571_;
v___y_545_ = v___y_567_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___x_586_;
goto v___jp_530_;
}
}
}
}
v___jp_589_:
{
if (lean_obj_tag(v___y_596_) == 0)
{
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_597_;
v___y_560_ = v___y_598_;
v___y_561_ = v___y_599_;
v___y_562_ = v___y_600_;
v___y_563_ = v___y_601_;
v___y_564_ = v___y_604_;
v___y_565_ = v___y_603_;
v___y_566_ = v___y_602_;
v___y_567_ = v___y_605_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_608_;
v___y_570_ = v___y_607_;
v___y_571_ = v___y_596_;
goto v___jp_552_;
}
else
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
v_val_609_ = lean_ctor_get(v___y_596_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___y_596_);
if (v_isSharedCheck_617_ == 0)
{
v___x_611_ = v___y_596_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v___y_596_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_597_;
v___y_560_ = v___y_598_;
v___y_561_ = v___y_599_;
v___y_562_ = v___y_600_;
v___y_563_ = v___y_601_;
v___y_564_ = v___y_604_;
v___y_565_ = v___y_603_;
v___y_566_ = v___y_602_;
v___y_567_ = v___y_605_;
v___y_568_ = v___y_606_;
v___y_569_ = v___y_608_;
v___y_570_ = v___y_607_;
v___y_571_ = v___x_615_;
goto v___jp_552_;
}
}
}
}
v___jp_618_:
{
if (lean_obj_tag(v___y_629_) == 0)
{
v___y_590_ = v___y_619_;
v___y_591_ = v___y_620_;
v___y_592_ = v___y_621_;
v___y_593_ = v___y_622_;
v___y_594_ = v___y_623_;
v___y_595_ = v___y_637_;
v___y_596_ = v___y_624_;
v___y_597_ = v___y_625_;
v___y_598_ = v___y_626_;
v___y_599_ = v___y_627_;
v___y_600_ = v___y_628_;
v___y_601_ = v___y_630_;
v___y_602_ = v___y_633_;
v___y_603_ = v___y_632_;
v___y_604_ = v___y_631_;
v___y_605_ = v___y_634_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_636_;
v___y_608_ = v___y_629_;
goto v___jp_589_;
}
else
{
lean_object* v_val_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
v_val_638_ = lean_ctor_get(v___y_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___y_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v___y_629_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_val_638_);
lean_dec(v___y_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v___y_590_ = v___y_619_;
v___y_591_ = v___y_620_;
v___y_592_ = v___y_621_;
v___y_593_ = v___y_622_;
v___y_594_ = v___y_623_;
v___y_595_ = v___y_637_;
v___y_596_ = v___y_624_;
v___y_597_ = v___y_625_;
v___y_598_ = v___y_626_;
v___y_599_ = v___y_627_;
v___y_600_ = v___y_628_;
v___y_601_ = v___y_630_;
v___y_602_ = v___y_633_;
v___y_603_ = v___y_632_;
v___y_604_ = v___y_631_;
v___y_605_ = v___y_634_;
v___y_606_ = v___y_635_;
v___y_607_ = v___y_636_;
v___y_608_ = v___x_644_;
goto v___jp_589_;
}
}
}
}
v___jp_647_:
{
if (lean_obj_tag(v___y_662_) == 0)
{
v___y_619_ = v___y_648_;
v___y_620_ = v___y_649_;
v___y_621_ = v___y_666_;
v___y_622_ = v___y_650_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
v___y_626_ = v___y_654_;
v___y_627_ = v___y_655_;
v___y_628_ = v___y_656_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_658_;
v___y_631_ = v___y_661_;
v___y_632_ = v___y_660_;
v___y_633_ = v___y_659_;
v___y_634_ = v___y_663_;
v___y_635_ = v___y_664_;
v___y_636_ = v___y_665_;
v___y_637_ = v___y_662_;
goto v___jp_618_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_682_; 
v_val_667_ = lean_ctor_get(v___y_662_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___y_662_);
if (v_isSharedCheck_682_ == 0)
{
v___x_669_ = v___y_662_;
v_isShared_670_ = v_isSharedCheck_682_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___y_662_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_682_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_str_675_; lean_object* v_startInclusive_676_; lean_object* v_endExclusive_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_string_utf8_byte_size(v_val_667_);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v_val_667_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = l_String_Slice_trimAscii(v___x_673_);
v_str_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc_ref(v_str_675_);
v_startInclusive_676_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_startInclusive_676_);
v_endExclusive_677_ = lean_ctor_get(v___x_674_, 2);
lean_inc(v_endExclusive_677_);
lean_dec_ref(v___x_674_);
v___x_678_ = lean_string_utf8_extract(v_str_675_, v_startInclusive_676_, v_endExclusive_677_);
lean_dec(v_endExclusive_677_);
lean_dec(v_startInclusive_676_);
lean_dec_ref(v_str_675_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_678_);
v___x_680_ = v___x_669_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_619_ = v___y_648_;
v___y_620_ = v___y_649_;
v___y_621_ = v___y_666_;
v___y_622_ = v___y_650_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
v___y_626_ = v___y_654_;
v___y_627_ = v___y_655_;
v___y_628_ = v___y_656_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_658_;
v___y_631_ = v___y_661_;
v___y_632_ = v___y_660_;
v___y_633_ = v___y_659_;
v___y_634_ = v___y_663_;
v___y_635_ = v___y_664_;
v___y_636_ = v___y_665_;
v___y_637_ = v___x_680_;
goto v___jp_618_;
}
}
}
}
v___jp_683_:
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_val_702_);
v___y_648_ = v___y_684_;
v___y_649_ = v___y_685_;
v___y_650_ = v___y_686_;
v___y_651_ = v___y_687_;
v___y_652_ = v___y_688_;
v___y_653_ = v___y_689_;
v___y_654_ = v___y_690_;
v___y_655_ = v___y_691_;
v___y_656_ = v___y_692_;
v___y_657_ = v___y_693_;
v___y_658_ = v___y_694_;
v___y_659_ = v___y_697_;
v___y_660_ = v___y_696_;
v___y_661_ = v___y_695_;
v___y_662_ = v___y_699_;
v___y_663_ = v___y_698_;
v___y_664_ = v___y_700_;
v___y_665_ = v___y_701_;
v___y_666_ = v___x_703_;
goto v___jp_647_;
}
v___jp_704_:
{
uint8_t v___x_722_; lean_object* v___x_723_; 
v___x_722_ = 0;
v___x_723_ = lean_box(0);
if (lean_obj_tag(v___y_706_) == 0)
{
if (lean_obj_tag(v___y_714_) == 0)
{
v___y_648_ = v___x_723_;
v___y_649_ = v___y_705_;
v___y_650_ = v___x_722_;
v___y_651_ = v___y_707_;
v___y_652_ = v___y_708_;
v___y_653_ = v___y_709_;
v___y_654_ = v___y_710_;
v___y_655_ = v___y_711_;
v___y_656_ = v___y_712_;
v___y_657_ = v___y_713_;
v___y_658_ = v___y_714_;
v___y_659_ = v___y_715_;
v___y_660_ = v___y_716_;
v___y_661_ = v___y_717_;
v___y_662_ = v___y_718_;
v___y_663_ = v___y_721_;
v___y_664_ = v___y_719_;
v___y_665_ = v___y_720_;
v___y_666_ = v___y_714_;
goto v___jp_647_;
}
else
{
lean_object* v_val_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_val_724_ = lean_ctor_get(v___y_714_, 0);
v___x_725_ = ((lean_object*)(l_Lake_Env_compute___closed__0));
lean_inc(v_val_724_);
v___x_726_ = l_System_FilePath_join(v_val_724_, v___x_725_);
v___x_727_ = ((lean_object*)(l_Lake_Env_compute___closed__1));
v___x_728_ = l_System_FilePath_join(v___x_726_, v___x_727_);
v___y_684_ = v___x_723_;
v___y_685_ = v___y_705_;
v___y_686_ = v___x_722_;
v___y_687_ = v___y_707_;
v___y_688_ = v___y_708_;
v___y_689_ = v___y_709_;
v___y_690_ = v___y_710_;
v___y_691_ = v___y_711_;
v___y_692_ = v___y_712_;
v___y_693_ = v___y_713_;
v___y_694_ = v___y_714_;
v___y_695_ = v___y_717_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_715_;
v___y_698_ = v___y_721_;
v___y_699_ = v___y_718_;
v___y_700_ = v___y_719_;
v___y_701_ = v___y_720_;
v_val_702_ = v___x_728_;
goto v___jp_683_;
}
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___y_706_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___y_706_, 1);
v___y_684_ = v___x_723_;
v___y_685_ = v___y_705_;
v___y_686_ = v___x_722_;
v___y_687_ = v___y_707_;
v___y_688_ = v___y_708_;
v___y_689_ = v___y_709_;
v___y_690_ = v___y_710_;
v___y_691_ = v___y_711_;
v___y_692_ = v___y_712_;
v___y_693_ = v___y_713_;
v___y_694_ = v___y_714_;
v___y_695_ = v___y_717_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_715_;
v___y_698_ = v___y_721_;
v___y_699_ = v___y_718_;
v___y_700_ = v___y_719_;
v___y_701_ = v___y_720_;
v_val_702_ = v_val_729_;
goto v___jp_683_;
}
}
v___jp_730_:
{
if (lean_obj_tag(v___y_739_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
v___y_705_ = v___y_731_;
v___y_706_ = v___y_732_;
v___y_707_ = v___y_733_;
v___y_708_ = v___y_734_;
v___y_709_ = v___y_735_;
v___y_710_ = v___y_736_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_738_;
v___y_713_ = v___y_740_;
v___y_714_ = v___y_741_;
v___y_715_ = v___y_743_;
v___y_716_ = v___y_744_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_745_;
v___y_719_ = v___y_747_;
v___y_720_ = v___y_746_;
v___y_721_ = v___x_748_;
goto v___jp_704_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_750_; 
v_val_749_ = lean_ctor_get(v___y_739_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v___y_739_, 1);
v___x_750_ = l_Lake_envToBool_x3f(v_val_749_);
v___y_705_ = v___y_731_;
v___y_706_ = v___y_732_;
v___y_707_ = v___y_733_;
v___y_708_ = v___y_734_;
v___y_709_ = v___y_735_;
v___y_710_ = v___y_736_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_738_;
v___y_713_ = v___y_740_;
v___y_714_ = v___y_741_;
v___y_715_ = v___y_743_;
v___y_716_ = v___y_744_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_745_;
v___y_719_ = v___y_747_;
v___y_720_ = v___y_746_;
v___y_721_ = v___x_750_;
goto v___jp_704_;
}
}
v___jp_751_:
{
if (lean_obj_tag(v___y_752_) == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
v___y_731_ = v___y_753_;
v___y_732_ = v___y_754_;
v___y_733_ = v___y_768_;
v___y_734_ = v___y_755_;
v___y_735_ = v___y_756_;
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_764_;
v___y_743_ = v___y_765_;
v___y_744_ = v___y_763_;
v___y_745_ = v___y_766_;
v___y_746_ = v___y_767_;
v___y_747_ = v___x_769_;
goto v___jp_730_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; 
v_val_770_ = lean_ctor_get(v___y_752_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___y_752_, 1);
v___x_771_ = l_Lake_envToBool_x3f(v_val_770_);
v___y_731_ = v___y_753_;
v___y_732_ = v___y_754_;
v___y_733_ = v___y_768_;
v___y_734_ = v___y_755_;
v___y_735_ = v___y_756_;
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_762_;
v___y_742_ = v___y_764_;
v___y_743_ = v___y_765_;
v___y_744_ = v___y_763_;
v___y_745_ = v___y_766_;
v___y_746_ = v___y_767_;
v___y_747_ = v___x_771_;
goto v___jp_730_;
}
}
v___jp_772_:
{
uint8_t v___x_789_; 
v___x_789_ = 0;
v___y_752_ = v___y_773_;
v___y_753_ = v___y_774_;
v___y_754_ = v___y_775_;
v___y_755_ = v___y_776_;
v___y_756_ = v___y_777_;
v___y_757_ = v___y_778_;
v___y_758_ = v___y_779_;
v___y_759_ = v___y_780_;
v___y_760_ = v___y_781_;
v___y_761_ = v___y_782_;
v___y_762_ = v___y_783_;
v___y_763_ = v___y_786_;
v___y_764_ = v___y_785_;
v___y_765_ = v___y_784_;
v___y_766_ = v___y_787_;
v___y_767_ = v___y_788_;
v___y_768_ = v___x_789_;
goto v___jp_751_;
}
v___jp_790_:
{
if (lean_obj_tag(v_noCache_528_) == 0)
{
if (lean_obj_tag(v___y_798_) == 0)
{
v___y_773_ = v___y_791_;
v___y_774_ = v___y_792_;
v___y_775_ = v___y_793_;
v___y_776_ = v___y_794_;
v___y_777_ = v___y_807_;
v___y_778_ = v___y_795_;
v___y_779_ = v___y_796_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_801_;
v___y_784_ = v___y_802_;
v___y_785_ = v___y_804_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_805_;
v___y_788_ = v___y_806_;
goto v___jp_772_;
}
else
{
lean_object* v_val_808_; lean_object* v___x_809_; 
v_val_808_ = lean_ctor_get(v___y_798_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___y_798_, 1);
v___x_809_ = l_Lake_envToBool_x3f(v_val_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
v___y_773_ = v___y_791_;
v___y_774_ = v___y_792_;
v___y_775_ = v___y_793_;
v___y_776_ = v___y_794_;
v___y_777_ = v___y_807_;
v___y_778_ = v___y_795_;
v___y_779_ = v___y_796_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_801_;
v___y_784_ = v___y_802_;
v___y_785_ = v___y_804_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_805_;
v___y_788_ = v___y_806_;
goto v___jp_772_;
}
else
{
lean_object* v_val_810_; uint8_t v___x_811_; 
v_val_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_unbox(v_val_810_);
lean_dec(v_val_810_);
v___y_752_ = v___y_791_;
v___y_753_ = v___y_792_;
v___y_754_ = v___y_793_;
v___y_755_ = v___y_794_;
v___y_756_ = v___y_807_;
v___y_757_ = v___y_795_;
v___y_758_ = v___y_796_;
v___y_759_ = v___y_797_;
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_801_;
v___y_763_ = v___y_803_;
v___y_764_ = v___y_804_;
v___y_765_ = v___y_802_;
v___y_766_ = v___y_805_;
v___y_767_ = v___y_806_;
v___y_768_ = v___x_811_;
goto v___jp_751_;
}
}
}
else
{
lean_object* v_val_812_; uint8_t v___x_813_; 
lean_dec(v___y_798_);
v_val_812_ = lean_ctor_get(v_noCache_528_, 0);
v___x_813_ = lean_unbox(v_val_812_);
v___y_752_ = v___y_791_;
v___y_753_ = v___y_792_;
v___y_754_ = v___y_793_;
v___y_755_ = v___y_794_;
v___y_756_ = v___y_807_;
v___y_757_ = v___y_795_;
v___y_758_ = v___y_796_;
v___y_759_ = v___y_797_;
v___y_760_ = v___y_799_;
v___y_761_ = v___y_800_;
v___y_762_ = v___y_801_;
v___y_763_ = v___y_803_;
v___y_764_ = v___y_804_;
v___y_765_ = v___y_802_;
v___y_766_ = v___y_805_;
v___y_767_ = v___y_806_;
v___y_768_ = v___x_813_;
goto v___jp_751_;
}
}
v___jp_814_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_819_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
v___x_820_ = lean_io_getenv(v___x_819_);
v___x_821_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
v___x_822_ = lean_io_getenv(v___x_821_);
v___x_823_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
v___x_824_ = lean_io_getenv(v___x_823_);
v___x_825_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
v___x_826_ = lean_io_getenv(v___x_825_);
v___x_827_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_828_ = lean_io_getenv(v___x_827_);
v___x_829_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_830_ = lean_io_getenv(v___x_829_);
v___x_831_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_832_ = lean_io_getenv(v___x_831_);
v___x_833_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
v___x_834_ = lean_io_getenv(v___x_833_);
v___x_835_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_836_ = lean_io_getenv(v___x_835_);
v___x_837_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_838_ = l_Lake_getSearchPath(v___x_837_);
v___x_839_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_840_ = l_Lake_getSearchPath(v___x_839_);
v___x_841_ = l_Lake_sharedLibPathEnvVar;
v___x_842_ = l_Lake_getSearchPath(v___x_841_);
v___x_843_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_844_ = l_Lake_getSearchPath(v___x_843_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lake_instInhabitedEnv_default___closed__0));
v___y_791_ = v___x_822_;
v___y_792_ = v_a_818_;
v___y_793_ = v___x_826_;
v___y_794_ = v___x_832_;
v___y_795_ = v___y_817_;
v___y_796_ = v___x_840_;
v___y_797_ = v___x_844_;
v___y_798_ = v___x_820_;
v___y_799_ = v___x_824_;
v___y_800_ = v___x_830_;
v___y_801_ = v___y_815_;
v___y_802_ = v___x_842_;
v___y_803_ = v___y_816_;
v___y_804_ = v___x_834_;
v___y_805_ = v___x_828_;
v___y_806_ = v___x_838_;
v___y_807_ = v___x_845_;
goto v___jp_790_;
}
else
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_836_, 1);
v___y_791_ = v___x_822_;
v___y_792_ = v_a_818_;
v___y_793_ = v___x_826_;
v___y_794_ = v___x_832_;
v___y_795_ = v___y_817_;
v___y_796_ = v___x_840_;
v___y_797_ = v___x_844_;
v___y_798_ = v___x_820_;
v___y_799_ = v___x_824_;
v___y_800_ = v___x_830_;
v___y_801_ = v___y_815_;
v___y_802_ = v___x_842_;
v___y_803_ = v___y_816_;
v___y_804_ = v___x_834_;
v___y_805_ = v___x_828_;
v___y_806_ = v___x_838_;
v___y_807_ = v_val_846_;
goto v___jp_790_;
}
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lake_Env_computeToolchain();
v___x_852_ = l_Lake_getUserHome_x3f();
v___x_853_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = ((lean_object*)(l_Lake_Env_compute___closed__15));
v___x_856_ = lean_io_getenv(v___x_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_val_857_; lean_object* v___x_858_; 
lean_dec_ref(v_a_850_);
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_857_);
v___y_815_ = v___x_852_;
v___y_816_ = v_a_854_;
v___y_817_ = v___x_851_;
v_a_818_ = v___x_858_;
goto v___jp_814_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v___x_856_);
v___x_859_ = ((lean_object*)(l_Lake_Env_compute___closed__16));
v___x_860_ = lean_string_append(v_a_850_, v___x_859_);
v___y_815_ = v___x_852_;
v___y_816_ = v_a_854_;
v___y_817_ = v___x_851_;
v_a_818_ = v___x_860_;
goto v___jp_814_;
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v___x_852_);
lean_dec_ref(v___x_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_elan_x3f_527_);
lean_dec_ref(v_lean_526_);
lean_dec_ref(v_lake_525_);
v_a_861_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_853_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_853_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute___boxed(lean_object* v_lake_872_, lean_object* v_lean_873_, lean_object* v_elan_x3f_874_, lean_object* v_noCache_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lake_Env_compute(v_lake_872_, v_lean_873_, v_elan_x3f_874_, v_noCache_875_);
lean_dec(v_noCache_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain(lean_object* v_env_878_){
_start:
{
lean_object* v_toolchain_879_; 
v_toolchain_879_ = lean_ctor_get(v_env_878_, 19);
lean_inc_ref(v_toolchain_879_);
return v_toolchain_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_cacheToolchain___boxed(lean_object* v_env_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lake_Env_cacheToolchain(v_env_880_);
lean_dec_ref(v_env_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* v_env_882_){
_start:
{
lean_object* v_lean_883_; lean_object* v_githashOverride_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_lean_883_ = lean_ctor_get(v_env_882_, 1);
v_githashOverride_884_ = lean_ctor_get(v_env_882_, 4);
v___x_885_ = lean_string_utf8_byte_size(v_githashOverride_884_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_nat_dec_eq(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_inc_ref(v_githashOverride_884_);
return v_githashOverride_884_;
}
else
{
lean_object* v_githash_888_; 
v_githash_888_ = lean_ctor_get(v_lean_883_, 1);
lean_inc_ref(v_githash_888_);
return v_githash_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* v_env_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lake_Env_leanGithash(v_env_889_);
lean_dec_ref(v_env_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* v_env_891_){
_start:
{
lean_object* v_lake_892_; lean_object* v_lean_893_; lean_object* v_initPath_894_; lean_object* v_binDir_895_; lean_object* v_binDir_896_; uint8_t v___x_897_; 
v_lake_892_ = lean_ctor_get(v_env_891_, 0);
v_lean_893_ = lean_ctor_get(v_env_891_, 1);
v_initPath_894_ = lean_ctor_get(v_env_891_, 18);
v_binDir_895_ = lean_ctor_get(v_lake_892_, 2);
v_binDir_896_ = lean_ctor_get(v_lean_893_, 6);
v___x_897_ = lean_string_dec_eq(v_binDir_895_, v_binDir_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc(v_initPath_894_);
lean_inc_ref(v_binDir_896_);
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v_binDir_896_);
lean_ctor_set(v___x_898_, 1, v_initPath_894_);
lean_inc_ref(v_binDir_895_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v_binDir_895_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
lean_inc(v_initPath_894_);
lean_inc_ref(v_binDir_896_);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v_binDir_896_);
lean_ctor_set(v___x_900_, 1, v_initPath_894_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* v_env_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_Env_path(v_env_901_);
lean_dec_ref(v_env_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* v_env_903_){
_start:
{
lean_object* v_lake_904_; lean_object* v_initLeanPath_905_; lean_object* v_libDir_906_; lean_object* v___x_907_; 
v_lake_904_ = lean_ctor_get(v_env_903_, 0);
v_initLeanPath_905_ = lean_ctor_get(v_env_903_, 15);
v_libDir_906_ = lean_ctor_get(v_lake_904_, 3);
lean_inc(v_initLeanPath_905_);
lean_inc_ref(v_libDir_906_);
v___x_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_907_, 0, v_libDir_906_);
lean_ctor_set(v___x_907_, 1, v_initLeanPath_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* v_env_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lake_Env_leanPath(v_env_908_);
lean_dec_ref(v_env_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* v_env_910_){
_start:
{
lean_object* v_lake_911_; lean_object* v_initLeanSrcPath_912_; lean_object* v_srcDir_913_; lean_object* v___x_914_; 
v_lake_911_ = lean_ctor_get(v_env_910_, 0);
v_initLeanSrcPath_912_ = lean_ctor_get(v_env_910_, 16);
v_srcDir_913_ = lean_ctor_get(v_lake_911_, 1);
lean_inc(v_initLeanSrcPath_912_);
lean_inc_ref(v_srcDir_913_);
v___x_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_914_, 0, v_srcDir_913_);
lean_ctor_set(v___x_914_, 1, v_initLeanSrcPath_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* v_env_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lake_Env_leanSrcPath(v_env_915_);
lean_dec_ref(v_env_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* v_env_917_){
_start:
{
lean_object* v_lean_918_; lean_object* v_initSharedLibPath_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_lean_918_ = lean_ctor_get(v_env_917_, 1);
lean_inc_ref(v_lean_918_);
v_initSharedLibPath_919_ = lean_ctor_get(v_env_917_, 17);
lean_inc(v_initSharedLibPath_919_);
lean_dec_ref(v_env_917_);
v___x_920_ = l_Lake_LeanInstall_sharedLibPath(v_lean_918_);
lean_dec_ref(v_lean_918_);
v___x_921_ = l_List_appendTR___redArg(v___x_920_, v_initSharedLibPath_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__14(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_952_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__0));
v___x_953_ = lean_unsigned_to_nat(9u);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_953_);
v___x_955_ = lean_array_push(v___x_954_, v___x_952_);
return v___x_955_;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars___closed__15(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__2));
v___x_957_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__14, &l_Lake_Env_noToolchainVars___closed__14_once, _init_l_Lake_Env_noToolchainVars___closed__14);
v___x_958_ = lean_array_push(v___x_957_, v___x_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars(lean_object* v_env_961_){
_start:
{
uint8_t v_noSystemCache_962_; lean_object* v_lakeSystemCache_x3f_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___y_967_; 
v_noSystemCache_962_ = lean_ctor_get_uint8(v_env_961_, sizeof(void*)*20 + 1);
v_lakeSystemCache_x3f_963_ = lean_ctor_get(v_env_961_, 9);
lean_inc(v_lakeSystemCache_x3f_963_);
lean_dec_ref(v_env_961_);
v___x_964_ = lean_box(0);
v___x_965_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (v_noSystemCache_962_ == 0)
{
if (lean_obj_tag(v_lakeSystemCache_x3f_963_) == 0)
{
v___y_967_ = v___x_964_;
goto v___jp_966_;
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_val_983_ = lean_ctor_get(v_lakeSystemCache_x3f_963_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_lakeSystemCache_x3f_963_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v_lakeSystemCache_x3f_963_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_val_983_);
lean_dec(v_lakeSystemCache_x3f_963_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v___y_967_ = v___x_988_;
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v___x_991_; 
lean_dec(v_lakeSystemCache_x3f_963_);
v___x_991_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_967_ = v___x_991_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v___y_967_);
v___x_969_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__4));
v___x_970_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__6));
v___x_971_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__8));
v___x_972_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__9));
v___x_973_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__11));
v___x_974_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__13));
v___x_975_ = lean_obj_once(&l_Lake_Env_noToolchainVars___closed__15, &l_Lake_Env_noToolchainVars___closed__15_once, _init_l_Lake_Env_noToolchainVars___closed__15);
v___x_976_ = lean_array_push(v___x_975_, v___x_968_);
v___x_977_ = lean_array_push(v___x_976_, v___x_969_);
v___x_978_ = lean_array_push(v___x_977_, v___x_970_);
v___x_979_ = lean_array_push(v___x_978_, v___x_971_);
v___x_980_ = lean_array_push(v___x_979_, v___x_972_);
v___x_981_ = lean_array_push(v___x_980_, v___x_973_);
v___x_982_ = lean_array_push(v___x_981_, v___x_974_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_box(1);
v___x_994_ = lean_panic_fn_borrowed(v___x_993_, v_msg_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_998_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_999_ = lean_unsigned_to_nat(35u);
v___x_1000_ = lean_unsigned_to_nat(182u);
v___x_1001_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1002_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1003_ = l_mkPanicMessageWithDecl(v___x_1002_, v___x_1001_, v___x_1000_, v___x_999_, v___x_998_);
return v___x_1003_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2));
v___x_1005_ = lean_unsigned_to_nat(21u);
v___x_1006_ = lean_unsigned_to_nat(183u);
v___x_1007_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1));
v___x_1008_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1009_ = l_mkPanicMessageWithDecl(v___x_1008_, v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_);
return v___x_1009_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1012_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1013_ = lean_unsigned_to_nat(35u);
v___x_1014_ = lean_unsigned_to_nat(276u);
v___x_1015_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1016_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1017_ = l_mkPanicMessageWithDecl(v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_, v___x_1012_);
return v___x_1017_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6));
v___x_1019_ = lean_unsigned_to_nat(21u);
v___x_1020_ = lean_unsigned_to_nat(277u);
v___x_1021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5));
v___x_1022_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0));
v___x_1023_ = l_mkPanicMessageWithDecl(v___x_1022_, v___x_1021_, v___x_1020_, v___x_1019_, v___x_1018_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(lean_object* v_k_1024_, lean_object* v_v_1025_, lean_object* v_t_1026_){
_start:
{
if (lean_obj_tag(v_t_1026_) == 0)
{
lean_object* v_size_1027_; lean_object* v_k_1028_; lean_object* v_v_1029_; lean_object* v_l_1030_; lean_object* v_r_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1387_; 
v_size_1027_ = lean_ctor_get(v_t_1026_, 0);
v_k_1028_ = lean_ctor_get(v_t_1026_, 1);
v_v_1029_ = lean_ctor_get(v_t_1026_, 2);
v_l_1030_ = lean_ctor_get(v_t_1026_, 3);
v_r_1031_ = lean_ctor_get(v_t_1026_, 4);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_t_1026_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1033_ = v_t_1026_;
v_isShared_1034_ = v_isSharedCheck_1387_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_r_1031_);
lean_inc(v_l_1030_);
lean_inc(v_v_1029_);
lean_inc(v_k_1028_);
lean_inc(v_size_1027_);
lean_dec(v_t_1026_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1387_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_string_compare(v_k_1024_, v_k_1028_);
switch(v___x_1035_)
{
case 0:
{
lean_object* v___x_1036_; 
lean_dec(v_size_1027_);
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1024_, v_v_1025_, v_l_1030_);
if (lean_obj_tag(v_r_1031_) == 0)
{
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_size_1037_; lean_object* v_size_1038_; lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v_l_1041_; lean_object* v_r_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_size_1037_ = lean_ctor_get(v_r_1031_, 0);
v_size_1038_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_size_1038_);
v_k_1039_ = lean_ctor_get(v___x_1036_, 1);
lean_inc(v_k_1039_);
v_v_1040_ = lean_ctor_get(v___x_1036_, 2);
lean_inc(v_v_1040_);
v_l_1041_ = lean_ctor_get(v___x_1036_, 3);
lean_inc(v_l_1041_);
v_r_1042_ = lean_ctor_get(v___x_1036_, 4);
lean_inc(v_r_1042_);
v___x_1043_ = lean_unsigned_to_nat(3u);
v___x_1044_ = lean_nat_mul(v___x_1043_, v_size_1037_);
v___x_1045_ = lean_nat_dec_lt(v___x_1044_, v_size_1038_);
lean_dec(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec(v_r_1042_);
lean_dec(v_l_1041_);
lean_dec(v_v_1040_);
lean_dec(v_k_1039_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v___x_1046_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1048_ = lean_nat_add(v___x_1047_, v_size_1037_);
lean_dec(v___x_1047_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v___x_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1048_);
v___x_1050_ = v___x_1033_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_r_1031_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1123_; 
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1124_ = lean_ctor_get(v___x_1036_, 4);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v___x_1036_, 3);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v___x_1036_, 2);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v___x_1036_, 1);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1128_);
v___x_1053_ = v___x_1036_;
v_isShared_1054_ = v_isSharedCheck_1123_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1036_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1123_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
if (lean_obj_tag(v_l_1041_) == 0)
{
if (lean_obj_tag(v_r_1042_) == 0)
{
lean_object* v_size_1055_; lean_object* v_size_1056_; lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v_l_1059_; lean_object* v_r_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_size_1055_ = lean_ctor_get(v_l_1041_, 0);
v_size_1056_ = lean_ctor_get(v_r_1042_, 0);
v_k_1057_ = lean_ctor_get(v_r_1042_, 1);
v_v_1058_ = lean_ctor_get(v_r_1042_, 2);
v_l_1059_ = lean_ctor_get(v_r_1042_, 3);
v_r_1060_ = lean_ctor_get(v_r_1042_, 4);
v___x_1061_ = lean_unsigned_to_nat(2u);
v___x_1062_ = lean_nat_mul(v___x_1061_, v_size_1055_);
v___x_1063_ = lean_nat_dec_lt(v_size_1056_, v___x_1062_);
lean_dec(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_r_1060_);
lean_inc(v_l_1059_);
lean_inc(v_v_1058_);
lean_inc(v_k_1057_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_r_1042_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1094_ = lean_ctor_get(v_r_1042_, 4);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_1042_, 3);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_r_1042_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_r_1042_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_r_1042_, 0);
lean_dec(v_unused_1098_);
v___x_1065_ = v_r_1042_;
v_isShared_1066_ = v_isSharedCheck_1093_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v_r_1042_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1093_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___x_1081_; lean_object* v___y_1083_; 
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_add(v___x_1067_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1069_ = lean_nat_add(v___x_1068_, v_size_1037_);
lean_dec(v___x_1068_);
v___x_1081_ = lean_nat_add(v___x_1067_, v_size_1055_);
if (lean_obj_tag(v_l_1059_) == 0)
{
lean_object* v_size_1091_; 
v_size_1091_ = lean_ctor_get(v_l_1059_, 0);
lean_inc(v_size_1091_);
v___y_1083_ = v_size_1091_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___y_1083_ = v___x_1092_;
goto v___jp_1082_;
}
v___jp_1070_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_nat_add(v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_r_1031_);
lean_ctor_set(v___x_1065_, 3, v_r_1060_);
lean_ctor_set(v___x_1065_, 2, v_v_1029_);
lean_ctor_set(v___x_1065_, 1, v_k_1028_);
lean_ctor_set(v___x_1065_, 0, v___x_1074_);
v___x_1076_ = v___x_1065_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_r_1060_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_r_1031_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v___x_1076_);
lean_ctor_set(v___x_1053_, 3, v___y_1071_);
lean_ctor_set(v___x_1053_, 2, v_v_1058_);
lean_ctor_set(v___x_1053_, 1, v_k_1057_);
lean_ctor_set(v___x_1053_, 0, v___x_1069_);
v___x_1078_ = v___x_1053_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___y_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_nat_add(v___x_1081_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec(v___x_1081_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1059_);
lean_ctor_set(v___x_1033_, 3, v_l_1041_);
lean_ctor_set(v___x_1033_, 2, v_v_1040_);
lean_ctor_set(v___x_1033_, 1, v_k_1039_);
lean_ctor_set(v___x_1033_, 0, v___x_1084_);
v___x_1086_ = v___x_1033_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_l_1041_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_l_1059_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_nat_add(v___x_1067_, v_size_1037_);
if (lean_obj_tag(v_r_1060_) == 0)
{
lean_object* v_size_1088_; 
v_size_1088_ = lean_ctor_get(v_r_1060_, 0);
lean_inc(v_size_1088_);
v___y_1071_ = v___x_1086_;
v___y_1072_ = v___x_1087_;
v___y_1073_ = v_size_1088_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___y_1071_ = v___x_1086_;
v___y_1072_ = v___x_1087_;
v___y_1073_ = v___x_1089_;
goto v___jp_1070_;
}
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_del_object(v___x_1033_);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v___x_1099_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1101_ = lean_nat_add(v___x_1100_, v_size_1037_);
lean_dec(v___x_1100_);
v___x_1102_ = lean_nat_add(v___x_1099_, v_size_1037_);
v___x_1103_ = lean_nat_add(v___x_1102_, v_size_1056_);
lean_dec(v___x_1102_);
lean_inc_ref(v_r_1031_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v_r_1031_);
lean_ctor_set(v___x_1053_, 3, v_r_1042_);
lean_ctor_set(v___x_1053_, 2, v_v_1029_);
lean_ctor_set(v___x_1053_, 1, v_k_1028_);
lean_ctor_set(v___x_1053_, 0, v___x_1103_);
v___x_1105_ = v___x_1053_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_r_1042_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_r_1031_);
v___x_1105_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_isSharedCheck_1112_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; 
v_unused_1113_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_r_1031_, 2);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_r_1031_, 1);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1117_);
v___x_1107_ = v_r_1031_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v_r_1031_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 4, v___x_1105_);
lean_ctor_set(v___x_1107_, 3, v_l_1041_);
lean_ctor_set(v___x_1107_, 2, v_v_1040_);
lean_ctor_set(v___x_1107_, 1, v_k_1039_);
lean_ctor_set(v___x_1107_, 0, v___x_1101_);
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_l_1041_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v___x_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref_known(v_l_1041_, 5);
lean_del_object(v___x_1053_);
lean_dec(v_v_1040_);
lean_dec(v_k_1039_);
lean_dec(v_size_1038_);
lean_dec_ref_known(v_r_1031_, 5);
lean_del_object(v___x_1033_);
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
v___x_1119_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
v___x_1120_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1119_);
return v___x_1120_;
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_del_object(v___x_1053_);
lean_dec(v_r_1042_);
lean_dec(v_v_1040_);
lean_dec(v_k_1039_);
lean_dec(v_size_1038_);
lean_dec_ref_known(v_r_1031_, 5);
lean_del_object(v___x_1033_);
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
v___x_1121_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
v___x_1122_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1121_);
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_size_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v_size_1129_ = lean_ctor_get(v_r_1031_, 0);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v___x_1130_, v_size_1129_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v___x_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1131_);
v___x_1133_ = v___x_1033_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_r_1031_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_l_1135_; 
v_l_1135_ = lean_ctor_get(v___x_1036_, 3);
lean_inc(v_l_1135_);
if (lean_obj_tag(v_l_1135_) == 0)
{
lean_object* v_r_1136_; 
v_r_1136_ = lean_ctor_get(v___x_1036_, 4);
lean_inc(v_r_1136_);
if (lean_obj_tag(v_r_1136_) == 0)
{
lean_object* v_size_1137_; lean_object* v_k_1138_; lean_object* v_v_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1153_; 
v_size_1137_ = lean_ctor_get(v___x_1036_, 0);
v_k_1138_ = lean_ctor_get(v___x_1036_, 1);
v_v_1139_ = lean_ctor_get(v___x_1036_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; 
v_unused_1154_ = lean_ctor_get(v___x_1036_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v___x_1036_, 3);
lean_dec(v_unused_1155_);
v___x_1141_ = v___x_1036_;
v_isShared_1142_ = v_isSharedCheck_1153_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_v_1139_);
lean_inc(v_k_1138_);
lean_inc(v_size_1137_);
lean_dec(v___x_1036_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1153_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_size_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_size_1143_ = lean_ctor_get(v_r_1136_, 0);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v___x_1144_, v_size_1137_);
lean_dec(v_size_1137_);
v___x_1146_ = lean_nat_add(v___x_1144_, v_size_1143_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 4, v_r_1031_);
lean_ctor_set(v___x_1141_, 3, v_r_1136_);
lean_ctor_set(v___x_1141_, 2, v_v_1029_);
lean_ctor_set(v___x_1141_, 1, v_k_1028_);
lean_ctor_set(v___x_1141_, 0, v___x_1146_);
v___x_1148_ = v___x_1141_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_r_1136_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_r_1031_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1148_);
lean_ctor_set(v___x_1033_, 3, v_l_1135_);
lean_ctor_set(v___x_1033_, 2, v_v_1139_);
lean_ctor_set(v___x_1033_, 1, v_k_1138_);
lean_ctor_set(v___x_1033_, 0, v___x_1145_);
v___x_1150_ = v___x_1033_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1139_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v_k_1156_; lean_object* v_v_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1169_; 
v_k_1156_ = lean_ctor_get(v___x_1036_, 1);
v_v_1157_ = lean_ctor_get(v___x_1036_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1170_ = lean_ctor_get(v___x_1036_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v___x_1036_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1172_);
v___x_1159_ = v___x_1036_;
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_v_1157_);
lean_inc(v_k_1156_);
lean_dec(v___x_1036_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1161_ = lean_unsigned_to_nat(3u);
v___x_1162_ = lean_unsigned_to_nat(1u);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 3, v_r_1136_);
lean_ctor_set(v___x_1159_, 2, v_v_1029_);
lean_ctor_set(v___x_1159_, 1, v_k_1028_);
lean_ctor_set(v___x_1159_, 0, v___x_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_r_1136_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_r_1136_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1164_);
lean_ctor_set(v___x_1033_, 3, v_l_1135_);
lean_ctor_set(v___x_1033_, 2, v_v_1157_);
lean_ctor_set(v___x_1033_, 1, v_k_1156_);
lean_ctor_set(v___x_1033_, 0, v___x_1161_);
v___x_1166_ = v___x_1033_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1156_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1157_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_l_1135_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
else
{
lean_object* v_r_1173_; 
v_r_1173_ = lean_ctor_get(v___x_1036_, 4);
lean_inc(v_r_1173_);
if (lean_obj_tag(v_r_1173_) == 0)
{
lean_object* v_k_1174_; lean_object* v_v_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1199_; 
v_k_1174_ = lean_ctor_get(v___x_1036_, 1);
v_v_1175_ = lean_ctor_get(v___x_1036_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; lean_object* v_unused_1202_; 
v_unused_1200_ = lean_ctor_get(v___x_1036_, 4);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v___x_1036_, 3);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1202_);
v___x_1177_ = v___x_1036_;
v_isShared_1178_ = v_isSharedCheck_1199_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_v_1175_);
lean_inc(v_k_1174_);
lean_dec(v___x_1036_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1199_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1195_; 
v_k_1179_ = lean_ctor_get(v_r_1173_, 1);
v_v_1180_ = lean_ctor_get(v_r_1173_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_r_1173_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1196_ = lean_ctor_get(v_r_1173_, 4);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_r_1173_, 3);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_r_1173_, 0);
lean_dec(v_unused_1198_);
v___x_1182_ = v_r_1173_;
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_v_1180_);
lean_inc(v_k_1179_);
lean_dec(v_r_1173_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = lean_unsigned_to_nat(3u);
v___x_1185_ = lean_unsigned_to_nat(1u);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 4, v_l_1135_);
lean_ctor_set(v___x_1182_, 3, v_l_1135_);
lean_ctor_set(v___x_1182_, 2, v_v_1175_);
lean_ctor_set(v___x_1182_, 1, v_k_1174_);
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1174_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1175_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_l_1135_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_l_1135_);
v___x_1187_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 4, v_l_1135_);
lean_ctor_set(v___x_1177_, 2, v_v_1029_);
lean_ctor_set(v___x_1177_, 1, v_k_1028_);
lean_ctor_set(v___x_1177_, 0, v___x_1185_);
v___x_1189_ = v___x_1177_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_l_1135_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_l_1135_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1189_);
lean_ctor_set(v___x_1033_, 3, v___x_1187_);
lean_ctor_set(v___x_1033_, 2, v_v_1180_);
lean_ctor_set(v___x_1033_, 1, v_k_1179_);
lean_ctor_set(v___x_1033_, 0, v___x_1184_);
v___x_1191_ = v___x_1033_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1179_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_unsigned_to_nat(2u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1173_);
lean_ctor_set(v___x_1033_, 3, v___x_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1203_);
v___x_1205_ = v___x_1033_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_r_1173_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1036_);
lean_ctor_set(v___x_1033_, 3, v___x_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1207_);
v___x_1209_ = v___x_1033_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v___x_1036_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
case 1:
{
lean_object* v___x_1212_; 
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 2, v_v_1025_);
lean_ctor_set(v___x_1033_, 1, v_k_1024_);
v___x_1212_ = v___x_1033_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_size_1027_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_1024_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_1025_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_r_1031_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
default: 
{
lean_object* v___x_1214_; 
lean_dec(v_size_1027_);
v___x_1214_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1024_, v_v_1025_, v_r_1031_);
if (lean_obj_tag(v_l_1030_) == 0)
{
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_size_1215_; lean_object* v_size_1216_; lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v_l_1219_; lean_object* v_r_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_size_1215_ = lean_ctor_get(v_l_1030_, 0);
v_size_1216_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_size_1216_);
v_k_1217_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_k_1217_);
v_v_1218_ = lean_ctor_get(v___x_1214_, 2);
lean_inc(v_v_1218_);
v_l_1219_ = lean_ctor_get(v___x_1214_, 3);
lean_inc(v_l_1219_);
v_r_1220_ = lean_ctor_get(v___x_1214_, 4);
lean_inc(v_r_1220_);
v___x_1221_ = lean_unsigned_to_nat(3u);
v___x_1222_ = lean_nat_mul(v___x_1221_, v_size_1215_);
v___x_1223_ = lean_nat_dec_lt(v___x_1222_, v_size_1216_);
lean_dec(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec(v_r_1220_);
lean_dec(v_l_1219_);
lean_dec(v_v_1218_);
lean_dec(v_k_1217_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v___x_1224_, v_size_1215_);
v___x_1226_ = lean_nat_add(v___x_1225_, v_size_1216_);
lean_dec(v_size_1216_);
lean_dec(v___x_1225_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1214_);
lean_ctor_set(v___x_1033_, 0, v___x_1226_);
v___x_1228_ = v___x_1033_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v___x_1214_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; 
v_unused_1300_ = lean_ctor_get(v___x_1214_, 4);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v___x_1214_, 3);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v___x_1214_, 2);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v___x_1214_, 1);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1304_);
v___x_1231_ = v___x_1214_;
v_isShared_1232_ = v_isSharedCheck_1299_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1214_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1299_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
if (lean_obj_tag(v_l_1219_) == 0)
{
if (lean_obj_tag(v_r_1220_) == 0)
{
lean_object* v_size_1233_; lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v_l_1236_; lean_object* v_r_1237_; lean_object* v_size_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_size_1233_ = lean_ctor_get(v_l_1219_, 0);
v_k_1234_ = lean_ctor_get(v_l_1219_, 1);
v_v_1235_ = lean_ctor_get(v_l_1219_, 2);
v_l_1236_ = lean_ctor_get(v_l_1219_, 3);
v_r_1237_ = lean_ctor_get(v_l_1219_, 4);
v_size_1238_ = lean_ctor_get(v_r_1220_, 0);
v___x_1239_ = lean_unsigned_to_nat(2u);
v___x_1240_ = lean_nat_mul(v___x_1239_, v_size_1238_);
v___x_1241_ = lean_nat_dec_lt(v_size_1233_, v___x_1240_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1270_; 
lean_inc(v_r_1237_);
lean_inc(v_l_1236_);
lean_inc(v_v_1235_);
lean_inc(v_k_1234_);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_l_1219_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; lean_object* v_unused_1272_; lean_object* v_unused_1273_; lean_object* v_unused_1274_; lean_object* v_unused_1275_; 
v_unused_1271_ = lean_ctor_get(v_l_1219_, 4);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_l_1219_, 3);
lean_dec(v_unused_1272_);
v_unused_1273_ = lean_ctor_get(v_l_1219_, 2);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v_l_1219_, 1);
lean_dec(v_unused_1274_);
v_unused_1275_ = lean_ctor_get(v_l_1219_, 0);
lean_dec(v_unused_1275_);
v___x_1243_ = v_l_1219_;
v_isShared_1244_ = v_isSharedCheck_1270_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_l_1219_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1270_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1260_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v___x_1245_, v_size_1215_);
v___x_1247_ = lean_nat_add(v___x_1246_, v_size_1216_);
lean_dec(v_size_1216_);
if (lean_obj_tag(v_l_1236_) == 0)
{
lean_object* v_size_1268_; 
v_size_1268_ = lean_ctor_get(v_l_1236_, 0);
lean_inc(v_size_1268_);
v___y_1260_ = v_size_1268_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
v___y_1260_ = v___x_1269_;
goto v___jp_1259_;
}
v___jp_1248_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_nat_add(v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_r_1220_);
lean_ctor_set(v___x_1243_, 3, v_r_1237_);
lean_ctor_set(v___x_1243_, 2, v_v_1218_);
lean_ctor_set(v___x_1243_, 1, v_k_1217_);
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_r_1237_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_r_1220_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1254_);
lean_ctor_set(v___x_1231_, 3, v___y_1249_);
lean_ctor_set(v___x_1231_, 2, v_v_1235_);
lean_ctor_set(v___x_1231_, 1, v_k_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1247_);
v___x_1256_ = v___x_1231_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_1234_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v___y_1249_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_nat_add(v___x_1246_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec(v___x_1246_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1236_);
lean_ctor_set(v___x_1033_, 0, v___x_1261_);
v___x_1263_ = v___x_1033_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_l_1236_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_nat_add(v___x_1245_, v_size_1238_);
if (lean_obj_tag(v_r_1237_) == 0)
{
lean_object* v_size_1265_; 
v_size_1265_ = lean_ctor_get(v_r_1237_, 0);
lean_inc(v_size_1265_);
v___y_1249_ = v___x_1263_;
v___y_1250_ = v___x_1264_;
v___y_1251_ = v_size_1265_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
v___y_1249_ = v___x_1263_;
v___y_1250_ = v___x_1264_;
v___y_1251_ = v___x_1266_;
goto v___jp_1248_;
}
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_del_object(v___x_1033_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_add(v___x_1276_, v_size_1215_);
v___x_1278_ = lean_nat_add(v___x_1277_, v_size_1216_);
lean_dec(v_size_1216_);
v___x_1279_ = lean_nat_add(v___x_1277_, v_size_1233_);
lean_dec(v___x_1277_);
lean_inc_ref(v_l_1030_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v_l_1219_);
lean_ctor_set(v___x_1231_, 3, v_l_1030_);
lean_ctor_set(v___x_1231_, 2, v_v_1029_);
lean_ctor_set(v___x_1231_, 1, v_k_1028_);
lean_ctor_set(v___x_1231_, 0, v___x_1279_);
v___x_1281_ = v___x_1231_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_l_1219_);
v___x_1281_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_isSharedCheck_1288_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; 
v_unused_1289_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1293_);
v___x_1283_ = v_l_1030_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_dec(v_l_1030_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 4, v_r_1220_);
lean_ctor_set(v___x_1283_, 3, v___x_1281_);
lean_ctor_set(v___x_1283_, 2, v_v_1218_);
lean_ctor_set(v___x_1283_, 1, v_k_1217_);
lean_ctor_set(v___x_1283_, 0, v___x_1278_);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_r_1220_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref_known(v_l_1219_, 5);
lean_del_object(v___x_1231_);
lean_dec(v_v_1218_);
lean_dec(v_k_1217_);
lean_dec(v_size_1216_);
lean_dec_ref_known(v_l_1030_, 5);
lean_del_object(v___x_1033_);
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
v___x_1295_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
v___x_1296_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1295_);
return v___x_1296_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_del_object(v___x_1231_);
lean_dec(v_r_1220_);
lean_dec(v_v_1218_);
lean_dec(v_k_1217_);
lean_dec(v_size_1216_);
lean_dec_ref_known(v_l_1030_, 5);
lean_del_object(v___x_1033_);
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
v___x_1297_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
v___x_1298_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_1297_);
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_size_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v_size_1305_ = lean_ctor_get(v_l_1030_, 0);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v___x_1306_, v_size_1305_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1214_);
lean_ctor_set(v___x_1033_, 0, v___x_1307_);
v___x_1309_ = v___x_1033_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v___x_1214_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_l_1311_; 
v_l_1311_ = lean_ctor_get(v___x_1214_, 3);
lean_inc(v_l_1311_);
if (lean_obj_tag(v_l_1311_) == 0)
{
lean_object* v_r_1312_; 
v_r_1312_ = lean_ctor_get(v___x_1214_, 4);
lean_inc(v_r_1312_);
if (lean_obj_tag(v_r_1312_) == 0)
{
lean_object* v_size_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
v_size_1313_ = lean_ctor_get(v___x_1214_, 0);
v_k_1314_ = lean_ctor_get(v___x_1214_, 1);
v_v_1315_ = lean_ctor_get(v___x_1214_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; lean_object* v_unused_1331_; 
v_unused_1330_ = lean_ctor_get(v___x_1214_, 4);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v___x_1214_, 3);
lean_dec(v_unused_1331_);
v___x_1317_ = v___x_1214_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_v_1315_);
lean_inc(v_k_1314_);
lean_inc(v_size_1313_);
lean_dec(v___x_1214_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_size_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v_size_1319_ = lean_ctor_get(v_l_1311_, 0);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v___x_1320_, v_size_1313_);
lean_dec(v_size_1313_);
v___x_1322_ = lean_nat_add(v___x_1320_, v_size_1319_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_l_1311_);
lean_ctor_set(v___x_1317_, 3, v_l_1030_);
lean_ctor_set(v___x_1317_, 2, v_v_1029_);
lean_ctor_set(v___x_1317_, 1, v_k_1028_);
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_l_1311_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1312_);
lean_ctor_set(v___x_1033_, 3, v___x_1324_);
lean_ctor_set(v___x_1033_, 2, v_v_1315_);
lean_ctor_set(v___x_1033_, 1, v_k_1314_);
lean_ctor_set(v___x_1033_, 0, v___x_1321_);
v___x_1326_ = v___x_1033_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_r_1312_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_k_1332_; lean_object* v_v_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1357_; 
v_k_1332_ = lean_ctor_get(v___x_1214_, 1);
v_v_1333_ = lean_ctor_get(v___x_1214_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; lean_object* v_unused_1360_; 
v_unused_1358_ = lean_ctor_get(v___x_1214_, 4);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v___x_1214_, 3);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1360_);
v___x_1335_ = v___x_1214_;
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_v_1333_);
lean_inc(v_k_1332_);
lean_dec(v___x_1214_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_k_1337_; lean_object* v_v_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1353_; 
v_k_1337_ = lean_ctor_get(v_l_1311_, 1);
v_v_1338_ = lean_ctor_get(v_l_1311_, 2);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_l_1311_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1354_ = lean_ctor_get(v_l_1311_, 4);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1311_, 3);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_l_1311_, 0);
lean_dec(v_unused_1356_);
v___x_1340_ = v_l_1311_;
v_isShared_1341_ = v_isSharedCheck_1353_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_v_1338_);
lean_inc(v_k_1337_);
lean_dec(v_l_1311_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1353_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(3u);
v___x_1343_ = lean_unsigned_to_nat(1u);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 4, v_r_1312_);
lean_ctor_set(v___x_1340_, 3, v_r_1312_);
lean_ctor_set(v___x_1340_, 2, v_v_1029_);
lean_ctor_set(v___x_1340_, 1, v_k_1028_);
lean_ctor_set(v___x_1340_, 0, v___x_1343_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_r_1312_);
v___x_1345_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 3, v_r_1312_);
lean_ctor_set(v___x_1335_, 0, v___x_1343_);
v___x_1347_ = v___x_1335_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_k_1332_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_v_1333_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_r_1312_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1347_);
lean_ctor_set(v___x_1033_, 3, v___x_1345_);
lean_ctor_set(v___x_1033_, 2, v_v_1338_);
lean_ctor_set(v___x_1033_, 1, v_k_1337_);
lean_ctor_set(v___x_1033_, 0, v___x_1342_);
v___x_1349_ = v___x_1033_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1361_; 
v_r_1361_ = lean_ctor_get(v___x_1214_, 4);
lean_inc(v_r_1361_);
if (lean_obj_tag(v_r_1361_) == 0)
{
lean_object* v_k_1362_; lean_object* v_v_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1375_; 
v_k_1362_ = lean_ctor_get(v___x_1214_, 1);
v_v_1363_ = lean_ctor_get(v___x_1214_, 2);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1376_ = lean_ctor_get(v___x_1214_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v___x_1214_, 3);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1378_);
v___x_1365_ = v___x_1214_;
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_v_1363_);
lean_inc(v_k_1362_);
lean_dec(v___x_1214_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = lean_unsigned_to_nat(3u);
v___x_1368_ = lean_unsigned_to_nat(1u);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 4, v_l_1311_);
lean_ctor_set(v___x_1365_, 2, v_v_1029_);
lean_ctor_set(v___x_1365_, 1, v_k_1028_);
lean_ctor_set(v___x_1365_, 0, v___x_1368_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_l_1311_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_l_1311_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1361_);
lean_ctor_set(v___x_1033_, 3, v___x_1370_);
lean_ctor_set(v___x_1033_, 2, v_v_1363_);
lean_ctor_set(v___x_1033_, 1, v_k_1362_);
lean_ctor_set(v___x_1033_, 0, v___x_1367_);
v___x_1372_ = v___x_1033_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1362_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1363_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1361_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = lean_unsigned_to_nat(2u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1214_);
lean_ctor_set(v___x_1033_, 3, v_r_1361_);
lean_ctor_set(v___x_1033_, 0, v___x_1379_);
v___x_1381_ = v___x_1033_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1361_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v___x_1214_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_unsigned_to_nat(1u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1214_);
lean_ctor_set(v___x_1033_, 3, v___x_1214_);
lean_ctor_set(v___x_1033_, 0, v___x_1383_);
v___x_1385_ = v___x_1033_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v___x_1214_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v_k_1024_);
lean_ctor_set(v___x_1389_, 2, v_v_1025_);
lean_ctor_set(v___x_1389_, 3, v_t_1026_);
lean_ctor_set(v___x_1389_, 4, v_t_1026_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(lean_object* v_init_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_k_1392_; lean_object* v_v_1393_; lean_object* v_l_1394_; lean_object* v_r_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_k_1392_ = lean_ctor_get(v_x_1391_, 1);
lean_inc(v_k_1392_);
v_v_1393_ = lean_ctor_get(v_x_1391_, 2);
lean_inc(v_v_1393_);
v_l_1394_ = lean_ctor_get(v_x_1391_, 3);
lean_inc(v_l_1394_);
v_r_1395_ = lean_ctor_get(v_x_1391_, 4);
lean_inc(v_r_1395_);
lean_dec_ref_known(v_x_1391_, 5);
v___x_1396_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1390_, v_l_1394_);
v___x_1397_ = 1;
v___x_1398_ = l_Lean_Name_toString(v_k_1392_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_v_1393_);
v___x_1400_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v___x_1398_, v___x_1399_, v___x_1396_);
v_init_1390_ = v___x_1400_;
v_x_1391_ = v_r_1395_;
goto _start;
}
else
{
return v_init_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(lean_object* v_m_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(1);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v___x_1403_, v_m_1402_);
v___x_1405_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* v_env_1411_){
_start:
{
lean_object* v_lake_1412_; lean_object* v_lean_1413_; lean_object* v_elan_x3f_1414_; lean_object* v_pkgUrlMap_1415_; uint8_t v_noCache_1416_; lean_object* v_lakeConfig_x3f_1417_; lean_object* v_cacheKey_x3f_1418_; lean_object* v_cacheArtifactEndpoint_x3f_1419_; lean_object* v_cacheRevisionEndpoint_x3f_1420_; lean_object* v_cacheService_x3f_1421_; lean_object* v_toolchain_1422_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___x_1551_; lean_object* v___y_1553_; 
v_lake_1412_ = lean_ctor_get(v_env_1411_, 0);
lean_inc_ref(v_lake_1412_);
v_lean_1413_ = lean_ctor_get(v_env_1411_, 1);
lean_inc_ref(v_lean_1413_);
v_elan_x3f_1414_ = lean_ctor_get(v_env_1411_, 2);
lean_inc(v_elan_x3f_1414_);
v_pkgUrlMap_1415_ = lean_ctor_get(v_env_1411_, 5);
lean_inc(v_pkgUrlMap_1415_);
v_noCache_1416_ = lean_ctor_get_uint8(v_env_1411_, sizeof(void*)*20);
v_lakeConfig_x3f_1417_ = lean_ctor_get(v_env_1411_, 10);
lean_inc(v_lakeConfig_x3f_1417_);
v_cacheKey_x3f_1418_ = lean_ctor_get(v_env_1411_, 11);
lean_inc(v_cacheKey_x3f_1418_);
v_cacheArtifactEndpoint_x3f_1419_ = lean_ctor_get(v_env_1411_, 12);
lean_inc(v_cacheArtifactEndpoint_x3f_1419_);
v_cacheRevisionEndpoint_x3f_1420_ = lean_ctor_get(v_env_1411_, 13);
lean_inc(v_cacheRevisionEndpoint_x3f_1420_);
v_cacheService_x3f_1421_ = lean_ctor_get(v_env_1411_, 14);
lean_inc(v_cacheService_x3f_1421_);
v_toolchain_1422_ = lean_ctor_get(v_env_1411_, 19);
lean_inc_ref(v_toolchain_1422_);
lean_dec_ref(v_env_1411_);
v___x_1551_ = ((lean_object*)(l_Lake_Env_baseVars___closed__3));
if (lean_obj_tag(v_elan_x3f_1414_) == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_box(0);
v___y_1553_ = v___x_1566_;
goto v___jp_1552_;
}
else
{
lean_object* v_val_1567_; lean_object* v_elan_1568_; lean_object* v___x_1569_; 
v_val_1567_ = lean_ctor_get(v_elan_x3f_1414_, 0);
v_elan_1568_ = lean_ctor_get(v_val_1567_, 1);
lean_inc_ref(v_elan_1568_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_elan_1568_);
v___y_1553_ = v___x_1569_;
goto v___jp_1552_;
}
v___jp_1423_:
{
lean_object* v_sysroot_1437_; lean_object* v_lean_1438_; lean_object* v_ar_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_sysroot_1437_ = lean_ctor_get(v_lean_1413_, 0);
v_lean_1438_ = lean_ctor_get(v_lean_1413_, 7);
v_ar_1439_ = lean_ctor_get(v_lean_1413_, 13);
lean_inc_ref(v___y_1432_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1432_);
lean_ctor_set(v___x_1440_, 1, v___y_1436_);
v___x_1441_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__7));
lean_inc_ref(v_lean_1438_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_lean_1438_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__10));
lean_inc_ref(v_sysroot_1437_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_sysroot_1437_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__12));
lean_inc_ref(v_ar_1439_);
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_ar_1439_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lake_Env_baseVars___closed__0));
v___x_1451_ = l_Lake_LeanInstall_leanCc_x3f(v_lean_1413_);
lean_dec_ref(v_lean_1413_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_unsigned_to_nat(16u);
v___x_1454_ = lean_mk_empty_array_with_capacity(v___x_1453_);
v___x_1455_ = lean_array_push(v___x_1454_, v___y_1429_);
v___x_1456_ = lean_array_push(v___x_1455_, v___y_1428_);
v___x_1457_ = lean_array_push(v___x_1456_, v___y_1435_);
v___x_1458_ = lean_array_push(v___x_1457_, v___y_1425_);
v___x_1459_ = lean_array_push(v___x_1458_, v___y_1434_);
v___x_1460_ = lean_array_push(v___x_1459_, v___y_1433_);
v___x_1461_ = lean_array_push(v___x_1460_, v___y_1427_);
v___x_1462_ = lean_array_push(v___x_1461_, v___y_1426_);
v___x_1463_ = lean_array_push(v___x_1462_, v___y_1430_);
v___x_1464_ = lean_array_push(v___x_1463_, v___y_1424_);
v___x_1465_ = lean_array_push(v___x_1464_, v___y_1431_);
v___x_1466_ = lean_array_push(v___x_1465_, v___x_1440_);
v___x_1467_ = lean_array_push(v___x_1466_, v___x_1443_);
v___x_1468_ = lean_array_push(v___x_1467_, v___x_1446_);
v___x_1469_ = lean_array_push(v___x_1468_, v___x_1449_);
v___x_1470_ = lean_array_push(v___x_1469_, v___x_1452_);
return v___x_1470_;
}
v___jp_1471_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_inc_ref(v___y_1480_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1480_);
lean_inc_ref(v___y_1473_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___y_1473_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lake_Env_compute___closed__6));
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_cacheKey_x3f_1418_);
v___x_1485_ = ((lean_object*)(l_Lake_Env_compute___closed__7));
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_cacheArtifactEndpoint_x3f_1419_);
v___x_1487_ = ((lean_object*)(l_Lake_Env_compute___closed__8));
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_cacheRevisionEndpoint_x3f_1420_);
v___x_1489_ = ((lean_object*)(l_Lake_Env_compute___closed__9));
if (lean_obj_tag(v_cacheService_x3f_1421_) == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_box(0);
v___y_1424_ = v___x_1486_;
v___y_1425_ = v___y_1472_;
v___y_1426_ = v___x_1482_;
v___y_1427_ = v___y_1476_;
v___y_1428_ = v___y_1475_;
v___y_1429_ = v___y_1474_;
v___y_1430_ = v___x_1484_;
v___y_1431_ = v___x_1488_;
v___y_1432_ = v___x_1489_;
v___y_1433_ = v___y_1477_;
v___y_1434_ = v___y_1479_;
v___y_1435_ = v___y_1478_;
v___y_1436_ = v___x_1490_;
goto v___jp_1423_;
}
else
{
lean_object* v_val_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
v_val_1491_ = lean_ctor_get(v_cacheService_x3f_1421_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_cacheService_x3f_1421_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v_cacheService_x3f_1421_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_val_1491_);
lean_dec(v_cacheService_x3f_1421_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_val_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
v___y_1424_ = v___x_1486_;
v___y_1425_ = v___y_1472_;
v___y_1426_ = v___x_1482_;
v___y_1427_ = v___y_1476_;
v___y_1428_ = v___y_1475_;
v___y_1429_ = v___y_1474_;
v___y_1430_ = v___x_1484_;
v___y_1431_ = v___x_1488_;
v___y_1432_ = v___x_1489_;
v___y_1433_ = v___y_1477_;
v___y_1434_ = v___y_1479_;
v___y_1435_ = v___y_1478_;
v___y_1436_ = v___x_1496_;
goto v___jp_1423_;
}
}
}
}
v___jp_1499_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc_ref(v___y_1505_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1505_);
lean_ctor_set(v___x_1507_, 1, v___y_1506_);
v___x_1508_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0));
v___x_1509_ = l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(v_pkgUrlMap_1415_);
v___x_1510_ = l_Lean_Json_compress(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1508_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = ((lean_object*)(l_Lake_Env_compute___closed__2));
if (v_noCache_1416_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = ((lean_object*)(l_Lake_Env_baseVars___closed__1));
v___y_1472_ = v___y_1500_;
v___y_1473_ = v___x_1513_;
v___y_1474_ = v___y_1502_;
v___y_1475_ = v___y_1501_;
v___y_1476_ = v___x_1512_;
v___y_1477_ = v___x_1507_;
v___y_1478_ = v___y_1504_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___x_1514_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1515_; 
v___x_1515_ = ((lean_object*)(l_Lake_Env_baseVars___closed__2));
v___y_1472_ = v___y_1500_;
v___y_1473_ = v___x_1513_;
v___y_1474_ = v___y_1502_;
v___y_1475_ = v___y_1501_;
v___y_1476_ = v___x_1512_;
v___y_1477_ = v___x_1507_;
v___y_1478_ = v___y_1504_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___x_1515_;
goto v___jp_1471_;
}
}
v___jp_1516_:
{
lean_object* v_home_1521_; lean_object* v_lake_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_home_1521_ = lean_ctor_get(v_lake_1412_, 0);
lean_inc_ref(v_home_1521_);
v_lake_1522_ = lean_ctor_get(v_lake_1412_, 5);
lean_inc_ref(v_lake_1522_);
lean_dec_ref(v_lake_1412_);
lean_inc_ref(v___y_1517_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___y_1517_);
lean_ctor_set(v___x_1523_, 1, v___y_1520_);
v___x_1524_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__1));
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_lake_1522_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__5));
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_home_1521_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Lake_Env_compute___closed__5));
if (lean_obj_tag(v_lakeConfig_x3f_1417_) == 1)
{
lean_object* v_val_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_val_1531_ = lean_ctor_get(v_lakeConfig_x3f_1417_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_lakeConfig_x3f_1417_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v_lakeConfig_x3f_1417_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_val_1531_);
lean_dec(v_lakeConfig_x3f_1417_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_val_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
v___y_1500_ = v___x_1526_;
v___y_1501_ = v___y_1519_;
v___y_1502_ = v___y_1518_;
v___y_1503_ = v___x_1529_;
v___y_1504_ = v___x_1523_;
v___y_1505_ = v___x_1530_;
v___y_1506_ = v___x_1536_;
goto v___jp_1499_;
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_lakeConfig_x3f_1417_);
v___x_1539_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1500_ = v___x_1526_;
v___y_1501_ = v___y_1519_;
v___y_1502_ = v___y_1518_;
v___y_1503_ = v___x_1529_;
v___y_1504_ = v___x_1523_;
v___y_1505_ = v___x_1530_;
v___y_1506_ = v___x_1539_;
goto v___jp_1499_;
}
}
v___jp_1540_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
lean_inc_ref(v___y_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___y_1542_);
lean_ctor_set(v___x_1544_, 1, v___y_1543_);
v___x_1545_ = ((lean_object*)(l_Lake_Env_computeToolchain___closed__0));
v___x_1546_ = lean_string_utf8_byte_size(v_toolchain_1422_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_toolchain_1422_);
v___y_1517_ = v___x_1545_;
v___y_1518_ = v___y_1541_;
v___y_1519_ = v___x_1544_;
v___y_1520_ = v___x_1549_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1550_; 
lean_dec_ref(v_toolchain_1422_);
v___x_1550_ = lean_box(0);
v___y_1517_ = v___x_1545_;
v___y_1518_ = v___y_1541_;
v___y_1519_ = v___x_1544_;
v___y_1520_ = v___x_1550_;
goto v___jp_1516_;
}
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___y_1553_);
v___x_1555_ = ((lean_object*)(l_Lake_Env_baseVars___closed__4));
if (lean_obj_tag(v_elan_x3f_1414_) == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_box(0);
v___y_1541_ = v___x_1554_;
v___y_1542_ = v___x_1555_;
v___y_1543_ = v___x_1556_;
goto v___jp_1540_;
}
else
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
v_val_1557_ = lean_ctor_get(v_elan_x3f_1414_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_elan_x3f_1414_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v_elan_x3f_1414_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v_elan_x3f_1414_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_home_1561_; lean_object* v___x_1563_; 
v_home_1561_ = lean_ctor_get(v_val_1557_, 0);
lean_inc_ref(v_home_1561_);
lean_dec(v_val_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v_home_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_home_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
v___y_1541_ = v___x_1554_;
v___y_1542_ = v___x_1555_;
v___y_1543_ = v___x_1563_;
goto v___jp_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1570_, lean_object* v_msg_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v_msg_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(lean_object* v_00_u03b2_1573_, lean_object* v_k_1574_, lean_object* v_v_1575_, lean_object* v_t_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_1574_, v_v_1575_, v_t_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(lean_object* v_init_1578_, lean_object* v_t_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_1578_, v_t_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0(lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__0___boxed(lean_object* v_x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lake_Env_vars___lam__0(v_x_1583_);
lean_dec(v_x_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1(uint8_t v_b_1589_){
_start:
{
if (v_b_1589_ == 0)
{
lean_object* v___x_1590_; 
v___x_1590_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__0));
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = ((lean_object*)(l_Lake_Env_vars___lam__1___closed__1));
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars___lam__1___boxed(lean_object* v_b_1592_){
_start:
{
uint8_t v_b_boxed_1593_; lean_object* v_res_1594_; 
v_b_boxed_1593_ = lean_unbox(v_b_1592_);
v_res_1594_ = l_Lake_Env_vars___lam__1(v_b_boxed_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* v_env_1595_){
_start:
{
lean_object* v_enableArtifactCache_x3f_1596_; lean_object* v_restoreAllArtifacts_x3f_1597_; lean_object* v_lakeCache_x3f_1598_; lean_object* v___x_1599_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___x_1652_; lean_object* v___y_1654_; 
v_enableArtifactCache_x3f_1596_ = lean_ctor_get(v_env_1595_, 6);
v_restoreAllArtifacts_x3f_1597_ = lean_ctor_get(v_env_1595_, 7);
v_lakeCache_x3f_1598_ = lean_ctor_get(v_env_1595_, 8);
lean_inc(v_lakeCache_x3f_1598_);
lean_inc_ref(v_env_1595_);
v___x_1599_ = l_Lake_Env_baseVars(v_env_1595_);
v___x_1652_ = ((lean_object*)(l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0));
if (lean_obj_tag(v_lakeCache_x3f_1598_) == 1)
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_val_1661_ = lean_ctor_get(v_lakeCache_x3f_1598_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_lakeCache_x3f_1598_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v_lakeCache_x3f_1598_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v_lakeCache_x3f_1598_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
v___y_1654_ = v___x_1666_;
goto v___jp_1653_;
}
}
}
else
{
lean_object* v___x_1669_; 
lean_dec(v_lakeCache_x3f_1598_);
v___x_1669_ = ((lean_object*)(l_Lake_Env_noToolchainVars___closed__16));
v___y_1654_ = v___x_1669_;
goto v___jp_1653_;
}
v___jp_1600_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_vars_1634_; uint8_t v___x_1635_; 
lean_inc_ref(v___y_1603_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1603_);
lean_ctor_set(v___x_1605_, 1, v___y_1604_);
v___x_1606_ = ((lean_object*)(l_Lake_Env_compute___closed__11));
v___x_1607_ = l_Lake_Env_leanPath(v_env_1595_);
v___x_1608_ = l_System_SearchPath_toString(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1606_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Lake_Env_compute___closed__12));
v___x_1612_ = l_Lake_Env_leanSrcPath(v_env_1595_);
v___x_1613_ = l_System_SearchPath_toString(v___x_1612_);
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1611_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Lake_Env_compute___closed__10));
v___x_1617_ = l_Lake_Env_leanGithash(v_env_1595_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Lake_Env_compute___closed__13));
v___x_1621_ = l_Lake_Env_path(v_env_1595_);
v___x_1622_ = l_System_SearchPath_toString(v___x_1621_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1620_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_unsigned_to_nat(7u);
v___x_1626_ = lean_mk_empty_array_with_capacity(v___x_1625_);
v___x_1627_ = lean_array_push(v___x_1626_, v___y_1601_);
v___x_1628_ = lean_array_push(v___x_1627_, v___y_1602_);
v___x_1629_ = lean_array_push(v___x_1628_, v___x_1605_);
v___x_1630_ = lean_array_push(v___x_1629_, v___x_1610_);
v___x_1631_ = lean_array_push(v___x_1630_, v___x_1615_);
v___x_1632_ = lean_array_push(v___x_1631_, v___x_1619_);
v___x_1633_ = lean_array_push(v___x_1632_, v___x_1624_);
v_vars_1634_ = l_Array_append___redArg(v___x_1599_, v___x_1633_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = l_System_Platform_isWindows;
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = l_Lake_sharedLibPathEnvVar;
v___x_1637_ = l_Lake_Env_sharedLibPath(v_env_1595_);
v___x_1638_ = l_System_SearchPath_toString(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1636_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_array_push(v_vars_1634_, v___x_1640_);
return v___x_1641_;
}
else
{
lean_dec_ref(v_env_1595_);
return v_vars_1634_;
}
}
v___jp_1642_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_inc_ref(v___y_1644_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1644_);
lean_ctor_set(v___x_1646_, 1, v___y_1645_);
v___x_1647_ = ((lean_object*)(l_Lake_Env_compute___closed__4));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1597_) == 1)
{
lean_object* v_val_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v_val_1648_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1597_, 0);
v___x_1649_ = lean_unbox(v_val_1648_);
v___x_1650_ = l_Lake_Env_vars___lam__1(v___x_1649_);
v___y_1601_ = v___y_1643_;
v___y_1602_ = v___x_1646_;
v___y_1603_ = v___x_1647_;
v___y_1604_ = v___x_1650_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lake_Env_vars___lam__0(v_restoreAllArtifacts_x3f_1597_);
v___y_1601_ = v___y_1643_;
v___y_1602_ = v___x_1646_;
v___y_1603_ = v___x_1647_;
v___y_1604_ = v___x_1651_;
goto v___jp_1600_;
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1652_);
lean_ctor_set(v___x_1655_, 1, v___y_1654_);
v___x_1656_ = ((lean_object*)(l_Lake_Env_compute___closed__3));
if (lean_obj_tag(v_enableArtifactCache_x3f_1596_) == 1)
{
lean_object* v_val_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v_val_1657_ = lean_ctor_get(v_enableArtifactCache_x3f_1596_, 0);
v___x_1658_ = lean_unbox(v_val_1657_);
v___x_1659_ = l_Lake_Env_vars___lam__1(v___x_1658_);
v___y_1643_ = v___x_1655_;
v___y_1644_ = v___x_1656_;
v___y_1645_ = v___x_1659_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lake_Env_vars___lam__0(v_enableArtifactCache_x3f_1596_);
v___y_1643_ = v___x_1655_;
v___y_1644_ = v___x_1656_;
v___y_1645_ = v___x_1660_;
goto v___jp_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* v_env_1670_){
_start:
{
lean_object* v_lake_1671_; lean_object* v_lean_1672_; lean_object* v_libDir_1673_; lean_object* v_leanLibDir_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_lake_1671_ = lean_ctor_get(v_env_1670_, 0);
v_lean_1672_ = lean_ctor_get(v_env_1670_, 1);
v_libDir_1673_ = lean_ctor_get(v_lake_1671_, 3);
v_leanLibDir_1674_ = lean_ctor_get(v_lean_1672_, 3);
v___x_1675_ = l_Lake_Env_leanPath(v_env_1670_);
lean_inc_ref(v_leanLibDir_1674_);
v___x_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_leanLibDir_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_inc_ref(v_libDir_1673_);
v___x_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_libDir_1673_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* v_env_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lake_Env_leanSearchPath(v_env_1678_);
lean_dec_ref(v_env_1678_);
return v_res_1679_;
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
