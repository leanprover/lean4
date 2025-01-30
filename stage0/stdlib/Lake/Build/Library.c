// Lean compiler output
// Module: Lake.Build.Library
// Imports: Lake.Build.Common Lake.Build.Targets
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__3;
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig;
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__1;
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_getModuleArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_mix___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_initLibraryFacetConfigs___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2;
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__5;
lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__3;
lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4;
static lean_object* l_Lake_LeanLib_recBuildShared___closed__1;
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nullFormat___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__6;
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig;
static lean_object* l_Lake_initLibraryFacetConfigs___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__3;
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_initLibraryFacetConfigs;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildExtraDepTargets___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__1(uint8_t, lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recBuildShared___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recBuildShared___spec__5___at_Lake_LeanLib_recBuildShared___spec__6(lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__4;
static lean_object* l_Lake_initLibraryFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__1;
extern lean_object* l_instMonadBaseIO;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__4;
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__5;
static lean_object* l_Lake_LeanLib_recCollectLocalModules_go___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__3;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__2;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__4;
static lean_object* l_Lake_LeanLib_recCollectLocalModules_go___closed__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recBuildShared___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__3;
static lean_object* l_Lake_initLibraryFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
static lean_object* l_Lake_LeanLib_recBuildExtraDepTargets___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__1;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1(lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__3;
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__1;
static lean_object* l_Lake_initLibraryFacetConfigs___closed__4;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_initLibraryFacetConfigs___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig___elambda__1(uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1;
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__5;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__7;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__4;
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__3;
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__4;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules_go___closed__3;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recBuildShared___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_37; 
x_37 = lean_usize_dec_lt(x_6, x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_uget(x_4, x_6);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
x_46 = l_Lake_LeanLibConfig_isLocalModule(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_12);
x_14 = x_48;
x_15 = x_13;
goto block_36;
}
else
{
lean_object* x_49; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_40, x_43, x_42, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
lean_ctor_set(x_7, 1, x_55);
lean_ctor_set(x_7, 0, x_56);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_7);
lean_ctor_set(x_50, 0, x_57);
x_14 = x_50;
x_15 = x_52;
goto block_36;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_7);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_14 = x_62;
x_15 = x_52;
goto block_36;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_free_object(x_7);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_dec(x_49);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
x_14 = x_50;
x_15 = x_63;
goto block_36;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_14 = x_67;
x_15 = x_63;
goto block_36;
}
}
}
else
{
uint8_t x_68; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_49);
if (x_68 == 0)
{
return x_49;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_49, 0);
x_70 = lean_ctor_get(x_49, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_49);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_7);
x_74 = lean_ctor_get(x_40, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
x_76 = l_Lake_LeanLibConfig_isLocalModule(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_40);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_12);
x_14 = x_79;
x_15 = x_13;
goto block_36;
}
else
{
lean_object* x_80; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_80 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_40, x_73, x_72, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
x_14 = x_90;
x_15 = x_83;
goto block_36;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_14 = x_95;
x_15 = x_91;
goto block_36;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_96 = lean_ctor_get(x_80, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_98 = x_80;
} else {
 lean_dec_ref(x_80);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
block_36:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_6 = x_28;
x_7 = x_26;
x_12 = x_25;
x_13 = x_15;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_15);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = l_Lean_Name_hash___override(x_27);
lean_dec(x_27);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imports", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recCollectLocalModules_go___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go___closed__1;
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = l_Lean_Name_hash___override(x_15);
lean_dec(x_15);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_13, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_2, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_31 = lean_ctor_get(x_4, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = l_Lake_LeanLib_recCollectLocalModules_go___closed__3;
lean_inc(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_35 = lean_apply_6(x_5, x_34, x_6, x_7, x_8, x_9, x_10);
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_add(x_12, x_222);
lean_dec(x_12);
x_224 = lean_box(0);
lean_inc(x_2);
x_225 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_225, 0, x_2);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_28);
x_226 = lean_array_uset(x_13, x_27, x_225);
x_227 = lean_unsigned_to_nat(4u);
x_228 = lean_nat_mul(x_223, x_227);
x_229 = lean_unsigned_to_nat(3u);
x_230 = lean_nat_div(x_228, x_229);
lean_dec(x_228);
x_231 = lean_array_get_size(x_226);
x_232 = lean_nat_dec_le(x_230, x_231);
lean_dec(x_231);
lean_dec(x_230);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_226);
lean_ctor_set(x_4, 1, x_233);
lean_ctor_set(x_4, 0, x_223);
x_36 = x_4;
goto block_221;
}
else
{
lean_ctor_set(x_4, 1, x_226);
lean_ctor_set(x_4, 0, x_223);
x_36 = x_4;
goto block_221;
}
block_221:
{
lean_object* x_37; lean_object* x_38; lean_object* x_78; lean_object* x_79; lean_object* x_95; lean_object* x_96; 
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_35, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_35, 1);
lean_inc(x_121);
lean_dec(x_35);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_io_wait(x_124, x_121);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_array_get_size(x_132);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_nat_dec_lt(x_134, x_133);
if (x_135 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_ctor_set(x_126, 1, x_123);
x_95 = x_126;
x_96 = x_128;
goto block_119;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_133, x_133);
if (x_136 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_ctor_set(x_126, 1, x_123);
x_95 = x_126;
x_96 = x_128;
goto block_119;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_free_object(x_126);
x_137 = 0;
x_138 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_139 = lean_box(0);
x_140 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_132, x_137, x_138, x_139, x_123, x_128);
lean_dec(x_132);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_141, 0);
lean_dec(x_144);
lean_ctor_set(x_141, 0, x_130);
x_95 = x_141;
x_96 = x_142;
goto block_119;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_130);
lean_ctor_set(x_146, 1, x_145);
x_95 = x_146;
x_96 = x_142;
goto block_119;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_126, 0);
lean_inc(x_147);
lean_dec(x_126);
x_148 = lean_ctor_get(x_127, 0);
lean_inc(x_148);
lean_dec(x_127);
x_149 = lean_array_get_size(x_148);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_nat_dec_lt(x_150, x_149);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_149);
lean_dec(x_148);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_123);
x_95 = x_152;
x_96 = x_128;
goto block_119;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_149, x_149);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_149);
lean_dec(x_148);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_123);
x_95 = x_154;
x_96 = x_128;
goto block_119;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_149);
lean_dec(x_149);
x_157 = lean_box(0);
x_158 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_148, x_155, x_156, x_157, x_123, x_128);
lean_dec(x_148);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_147);
lean_ctor_set(x_163, 1, x_161);
x_95 = x_163;
x_96 = x_160;
goto block_119;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_126, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_125, 1);
lean_inc(x_165);
lean_dec(x_125);
x_166 = !lean_is_exclusive(x_126);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_126, 0);
x_168 = lean_ctor_get(x_126, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_array_get_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_lt(x_171, x_170);
if (x_172 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_126, 1, x_123);
x_95 = x_126;
x_96 = x_165;
goto block_119;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_126, 1, x_123);
x_95 = x_126;
x_96 = x_165;
goto block_119;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_126);
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_176 = lean_box(0);
x_177 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_169, x_174, x_175, x_176, x_123, x_165);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_178, 0);
lean_dec(x_181);
lean_ctor_set_tag(x_178, 1);
lean_ctor_set(x_178, 0, x_167);
x_95 = x_178;
x_96 = x_179;
goto block_119;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_167);
lean_ctor_set(x_183, 1, x_182);
x_95 = x_183;
x_96 = x_179;
goto block_119;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_126, 0);
lean_inc(x_184);
lean_dec(x_126);
x_185 = lean_ctor_get(x_164, 0);
lean_inc(x_185);
lean_dec(x_164);
x_186 = lean_array_get_size(x_185);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_nat_dec_lt(x_187, x_186);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_123);
x_95 = x_189;
x_96 = x_165;
goto block_119;
}
else
{
uint8_t x_190; 
x_190 = lean_nat_dec_le(x_186, x_186);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_186);
lean_dec(x_185);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_123);
x_95 = x_191;
x_96 = x_165;
goto block_119;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_194 = lean_box(0);
x_195 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_185, x_192, x_193, x_194, x_123, x_165);
lean_dec(x_185);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_184);
lean_ctor_set(x_200, 1, x_198);
x_95 = x_200;
x_96 = x_197;
goto block_119;
}
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_123);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_201 = !lean_is_exclusive(x_125);
if (x_201 == 0)
{
return x_125;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_125, 0);
x_203 = lean_ctor_get(x_125, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_125);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_35);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_35, 0);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_120);
if (x_207 == 0)
{
return x_35;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_120, 0);
x_209 = lean_ctor_get(x_120, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_120);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_35, 0, x_210);
return x_35;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_35, 1);
lean_inc(x_211);
lean_dec(x_35);
x_212 = lean_ctor_get(x_120, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_120, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_214 = x_120;
} else {
 lean_dec_ref(x_120);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_211);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_217 = !lean_is_exclusive(x_35);
if (x_217 == 0)
{
return x_35;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_35, 0);
x_219 = lean_ctor_get(x_35, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_35);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
block_77:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_3);
x_43 = lean_array_size(x_39);
x_44 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_39, x_41, x_39, x_43, x_44, x_42, x_5, x_6, x_7, x_8, x_40, x_38);
lean_dec(x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_array_push(x_51, x_2);
x_53 = lean_box(0);
x_54 = lean_apply_9(x_11, x_50, x_52, x_53, x_5, x_6, x_7, x_8, x_49, x_48);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_45, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_45, 0, x_60);
return x_45;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_dec(x_45);
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_64 = x_46;
} else {
 lean_dec_ref(x_46);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_45);
if (x_67 == 0)
{
return x_45;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_37);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_37);
lean_ctor_set(x_72, 1, x_38);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_37, 0);
x_74 = lean_ctor_get(x_37, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_37);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_38);
return x_76;
}
}
}
block_94:
{
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
lean_ctor_set(x_78, 1, x_82);
x_37 = x_78;
x_38 = x_79;
goto block_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_78, 0);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_78);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_37 = x_86;
x_38 = x_79;
goto block_77;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_78);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_78, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
lean_ctor_set(x_78, 1, x_89);
x_37 = x_78;
x_38 = x_79;
goto block_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_78, 0);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_78);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_37 = x_93;
x_38 = x_79;
goto block_77;
}
}
}
block_119:
{
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_95, 1);
x_99 = 0;
x_100 = l_Lake_BuildTrace_nil;
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_99);
lean_ctor_set(x_95, 1, x_101);
x_78 = x_95;
x_79 = x_96;
goto block_94;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_95, 0);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_95);
x_104 = 0;
x_105 = l_Lake_BuildTrace_nil;
x_106 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
x_78 = x_107;
x_79 = x_96;
goto block_94;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_95);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_95, 1);
x_110 = 0;
x_111 = l_Lake_BuildTrace_nil;
x_112 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_110);
lean_ctor_set(x_95, 1, x_112);
x_78 = x_95;
x_79 = x_96;
goto block_94;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_95, 0);
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_95);
x_115 = 0;
x_116 = l_Lake_BuildTrace_nil;
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_115);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_78 = x_118;
x_79 = x_96;
goto block_94;
}
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
lean_dec(x_4);
x_234 = l_Lake_LeanLib_recCollectLocalModules_go___closed__3;
lean_inc(x_2);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_2);
lean_ctor_set(x_235, 1, x_234);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_236 = lean_apply_6(x_5, x_235, x_6, x_7, x_8, x_9, x_10);
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_nat_add(x_12, x_366);
lean_dec(x_12);
x_368 = lean_box(0);
lean_inc(x_2);
x_369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_369, 0, x_2);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_28);
x_370 = lean_array_uset(x_13, x_27, x_369);
x_371 = lean_unsigned_to_nat(4u);
x_372 = lean_nat_mul(x_367, x_371);
x_373 = lean_unsigned_to_nat(3u);
x_374 = lean_nat_div(x_372, x_373);
lean_dec(x_372);
x_375 = lean_array_get_size(x_370);
x_376 = lean_nat_dec_le(x_374, x_375);
lean_dec(x_375);
lean_dec(x_374);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_370);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_367);
lean_ctor_set(x_378, 1, x_377);
x_237 = x_378;
goto block_365;
}
else
{
lean_object* x_379; 
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_367);
lean_ctor_set(x_379, 1, x_370);
x_237 = x_379;
goto block_365;
}
block_365:
{
lean_object* x_238; lean_object* x_239; lean_object* x_273; lean_object* x_274; lean_object* x_286; lean_object* x_287; 
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_236, 0);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_236, 1);
lean_inc(x_304);
lean_dec(x_236);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_io_wait(x_307, x_304);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_ctor_get(x_309, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_313 = x_309;
} else {
 lean_dec_ref(x_309);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_310, 0);
lean_inc(x_314);
lean_dec(x_310);
x_315 = lean_array_get_size(x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = lean_nat_dec_lt(x_316, x_315);
if (x_317 == 0)
{
lean_object* x_318; 
lean_dec(x_315);
lean_dec(x_314);
if (lean_is_scalar(x_313)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_313;
}
lean_ctor_set(x_318, 0, x_312);
lean_ctor_set(x_318, 1, x_306);
x_286 = x_318;
x_287 = x_311;
goto block_302;
}
else
{
uint8_t x_319; 
x_319 = lean_nat_dec_le(x_315, x_315);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_315);
lean_dec(x_314);
if (lean_is_scalar(x_313)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_313;
}
lean_ctor_set(x_320, 0, x_312);
lean_ctor_set(x_320, 1, x_306);
x_286 = x_320;
x_287 = x_311;
goto block_302;
}
else
{
size_t x_321; size_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_313);
x_321 = 0;
x_322 = lean_usize_of_nat(x_315);
lean_dec(x_315);
x_323 = lean_box(0);
x_324 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_314, x_321, x_322, x_323, x_306, x_311);
lean_dec(x_314);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_312);
lean_ctor_set(x_329, 1, x_327);
x_286 = x_329;
x_287 = x_326;
goto block_302;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_330 = lean_ctor_get(x_309, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_308, 1);
lean_inc(x_331);
lean_dec(x_308);
x_332 = lean_ctor_get(x_309, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_333 = x_309;
} else {
 lean_dec_ref(x_309);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_330, 0);
lean_inc(x_334);
lean_dec(x_330);
x_335 = lean_array_get_size(x_334);
x_336 = lean_unsigned_to_nat(0u);
x_337 = lean_nat_dec_lt(x_336, x_335);
if (x_337 == 0)
{
lean_object* x_338; 
lean_dec(x_335);
lean_dec(x_334);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_333;
}
lean_ctor_set(x_338, 0, x_332);
lean_ctor_set(x_338, 1, x_306);
x_286 = x_338;
x_287 = x_331;
goto block_302;
}
else
{
uint8_t x_339; 
x_339 = lean_nat_dec_le(x_335, x_335);
if (x_339 == 0)
{
lean_object* x_340; 
lean_dec(x_335);
lean_dec(x_334);
if (lean_is_scalar(x_333)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_333;
}
lean_ctor_set(x_340, 0, x_332);
lean_ctor_set(x_340, 1, x_306);
x_286 = x_340;
x_287 = x_331;
goto block_302;
}
else
{
size_t x_341; size_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_333);
x_341 = 0;
x_342 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_343 = lean_box(0);
x_344 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_334, x_341, x_342, x_343, x_306, x_331);
lean_dec(x_334);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
 lean_ctor_set_tag(x_349, 1);
}
lean_ctor_set(x_349, 0, x_332);
lean_ctor_set(x_349, 1, x_347);
x_286 = x_349;
x_287 = x_346;
goto block_302;
}
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_306);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_350 = lean_ctor_get(x_308, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_308, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_352 = x_308;
} else {
 lean_dec_ref(x_308);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_354 = lean_ctor_get(x_236, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_355 = x_236;
} else {
 lean_dec_ref(x_236);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_303, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_303, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_358 = x_303;
} else {
 lean_dec_ref(x_303);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
if (lean_is_scalar(x_355)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_355;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_354);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_ctor_get(x_236, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_236, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_363 = x_236;
} else {
 lean_dec_ref(x_236);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
block_272:
{
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; size_t x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_3);
x_244 = lean_array_size(x_240);
x_245 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_246 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_240, x_242, x_240, x_244, x_245, x_243, x_5, x_6, x_7, x_8, x_241, x_239);
lean_dec(x_240);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_ctor_get(x_248, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_248, 1);
lean_inc(x_252);
lean_dec(x_248);
x_253 = lean_array_push(x_252, x_2);
x_254 = lean_box(0);
x_255 = lean_apply_9(x_11, x_251, x_253, x_254, x_5, x_6, x_7, x_8, x_250, x_249);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_256 = lean_ctor_get(x_246, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_257 = x_246;
} else {
 lean_dec_ref(x_246);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_247, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_247, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_260 = x_247;
} else {
 lean_dec_ref(x_247);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_263 = lean_ctor_get(x_246, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_246, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_265 = x_246;
} else {
 lean_dec_ref(x_246);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_267 = lean_ctor_get(x_238, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_238, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_269 = x_238;
} else {
 lean_dec_ref(x_238);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_239);
return x_271;
}
}
block_285:
{
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_277 = x_273;
} else {
 lean_dec_ref(x_273);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_278);
x_238 = x_279;
x_239 = x_274;
goto block_272;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_273, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_273, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_282 = x_273;
} else {
 lean_dec_ref(x_273);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
lean_dec(x_281);
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_283);
x_238 = x_284;
x_239 = x_274;
goto block_272;
}
}
block_302:
{
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_290 = x_286;
} else {
 lean_dec_ref(x_286);
 x_290 = lean_box(0);
}
x_291 = 0;
x_292 = l_Lake_BuildTrace_nil;
x_293 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_293, 0, x_289);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*2, x_291);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_293);
x_273 = x_294;
x_274 = x_287;
goto block_285;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_295 = lean_ctor_get(x_286, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_286, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_297 = x_286;
} else {
 lean_dec_ref(x_286);
 x_297 = lean_box(0);
}
x_298 = 0;
x_299 = l_Lake_BuildTrace_nil;
x_300 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*2, x_298);
if (lean_is_scalar(x_297)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_297;
}
lean_ctor_set(x_301, 0, x_295);
lean_ctor_set(x_301, 1, x_300);
x_273 = x_301;
x_274 = x_287;
goto block_285;
}
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_380 = lean_box(0);
x_381 = lean_apply_9(x_11, x_4, x_3, x_380, x_5, x_6, x_7, x_8, x_9, x_10);
return x_381;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_17, x_19, x_18, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_6, x_28);
x_6 = x_29;
x_7 = x_22;
x_12 = x_24;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_7 = x_33;
x_12 = x_24;
x_13 = x_23;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_42);
return x_20;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_46 = x_21;
} else {
 lean_dec_ref(x_21);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_2, x_12, x_3, x_4, x_5, x_6, x_13, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_LeanLib_getModuleArray(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_io_error_to_string(x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_6);
x_22 = lean_array_push(x_6, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_io_error_to_string(x_24);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_6);
x_30 = lean_array_push(x_6, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_array_size(x_3);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(x_2, x_3, x_10, x_3, x_13, x_14, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = l_Lake_BuildTrace_nil;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_24);
x_29 = lean_task_pure(x_16);
x_30 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_31 = 0;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_32);
lean_ctor_set(x_15, 0, x_17);
return x_15;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_33);
x_37 = lean_task_pure(x_16);
x_38 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_39 = 0;
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_15, 0, x_41);
return x_15;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_44 = x_17;
} else {
 lean_dec_ref(x_17);
 x_44 = lean_box(0);
}
x_45 = 0;
x_46 = l_Lake_BuildTrace_nil;
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_task_pure(x_48);
x_50 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_51 = 0;
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_51);
if (lean_is_scalar(x_44)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_44;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_15, 0, x_53);
return x_15;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_56 = x_16;
} else {
 lean_dec_ref(x_16);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_58 = x_17;
} else {
 lean_dec_ref(x_17);
 x_58 = lean_box(0);
}
x_59 = 0;
x_60 = l_Lake_BuildTrace_nil;
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_59);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_task_pure(x_62);
x_64 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_65 = 0;
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_65);
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_54);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_15, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
return x_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_16, 0);
x_73 = lean_ctor_get(x_16, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_16);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_15, 0, x_74);
return x_15;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_15, 1);
lean_inc(x_75);
lean_dec(x_15);
x_76 = lean_ctor_get(x_16, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_16, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_78 = x_16;
} else {
 lean_dec_ref(x_16);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_15);
if (x_81 == 0)
{
return x_15;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_15, 0);
x_83 = lean_ctor_get(x_15, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_15);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_10 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed), 9, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lake_ensureJob___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_LeanLib_recCollectLocalModules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_LeanLib_recCollectLocalModules___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_string_append(x_8, x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = 1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1;
x_13 = l_Lean_Name_toString(x_10, x_11, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_16;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1;
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3;
x_4 = l_Substring_prevn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2(x_2, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_string_utf8_byte_size(x_12);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_nat_sub(x_13, x_4);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_prevn(x_14, x_16, x_15);
lean_dec(x_14);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_17);
x_19 = lean_string_utf8_extract(x_12, x_4, x_18);
lean_dec(x_18);
lean_dec(x_12);
return x_19;
}
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_size(x_2);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3(x_20, x_21, x_2);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Json_compress(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("modules", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_modulesFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__3;
x_2 = 0;
x_3 = l_Lake_LeanLib_modulesFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_modulesFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_6(x_5, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lake_Job_mix___rarg(x_4, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_20;
x_9 = x_19;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_9);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
return x_41;
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recBuildLean___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__2;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__3;
x_2 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_48; lean_object* x_49; lean_object* x_65; lean_object* x_66; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_92 = lean_apply_6(x_2, x_91, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_io_wait(x_97, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_array_get_size(x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_lt(x_107, x_106);
if (x_108 == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_ctor_set(x_99, 1, x_96);
x_65 = x_99;
x_66 = x_101;
goto block_89;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_106, x_106);
if (x_109 == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_ctor_set(x_99, 1, x_96);
x_65 = x_99;
x_66 = x_101;
goto block_89;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_free_object(x_99);
x_110 = 0;
x_111 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_105, x_110, x_111, x_112, x_96, x_101);
lean_dec(x_105);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_114, 0);
lean_dec(x_117);
lean_ctor_set(x_114, 0, x_103);
x_65 = x_114;
x_66 = x_115;
goto block_89;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_103);
lean_ctor_set(x_119, 1, x_118);
x_65 = x_119;
x_66 = x_115;
goto block_89;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_99, 0);
lean_inc(x_120);
lean_dec(x_99);
x_121 = lean_ctor_get(x_100, 0);
lean_inc(x_121);
lean_dec(x_100);
x_122 = lean_array_get_size(x_121);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_nat_dec_lt(x_123, x_122);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_122);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_96);
x_65 = x_125;
x_66 = x_101;
goto block_89;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_le(x_122, x_122);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_122);
lean_dec(x_121);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_96);
x_65 = x_127;
x_66 = x_101;
goto block_89;
}
else
{
size_t x_128; size_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = 0;
x_129 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_130 = lean_box(0);
x_131 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_121, x_128, x_129, x_130, x_96, x_101);
lean_dec(x_121);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_120);
lean_ctor_set(x_136, 1, x_134);
x_65 = x_136;
x_66 = x_133;
goto block_89;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_99, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_98, 1);
lean_inc(x_138);
lean_dec(x_98);
x_139 = !lean_is_exclusive(x_99);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_140 = lean_ctor_get(x_99, 0);
x_141 = lean_ctor_get(x_99, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
x_143 = lean_array_get_size(x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_nat_dec_lt(x_144, x_143);
if (x_145 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
lean_ctor_set(x_99, 1, x_96);
x_65 = x_99;
x_66 = x_138;
goto block_89;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_143, x_143);
if (x_146 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
lean_ctor_set(x_99, 1, x_96);
x_65 = x_99;
x_66 = x_138;
goto block_89;
}
else
{
size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_free_object(x_99);
x_147 = 0;
x_148 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_149 = lean_box(0);
x_150 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_142, x_147, x_148, x_149, x_96, x_138);
lean_dec(x_142);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_151, 0);
lean_dec(x_154);
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 0, x_140);
x_65 = x_151;
x_66 = x_152;
goto block_89;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_140);
lean_ctor_set(x_156, 1, x_155);
x_65 = x_156;
x_66 = x_152;
goto block_89;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_99, 0);
lean_inc(x_157);
lean_dec(x_99);
x_158 = lean_ctor_get(x_137, 0);
lean_inc(x_158);
lean_dec(x_137);
x_159 = lean_array_get_size(x_158);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_lt(x_160, x_159);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_159);
lean_dec(x_158);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_96);
x_65 = x_162;
x_66 = x_138;
goto block_89;
}
else
{
uint8_t x_163; 
x_163 = lean_nat_dec_le(x_159, x_159);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_159);
lean_dec(x_158);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_96);
x_65 = x_164;
x_66 = x_138;
goto block_89;
}
else
{
size_t x_165; size_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = 0;
x_166 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_167 = lean_box(0);
x_168 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_158, x_165, x_166, x_167, x_96, x_138);
lean_dec(x_158);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_157);
lean_ctor_set(x_173, 1, x_171);
x_65 = x_173;
x_66 = x_170;
goto block_89;
}
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_98);
if (x_174 == 0)
{
return x_98;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_98, 0);
x_176 = lean_ctor_get(x_98, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_98);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_92);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_92, 0);
lean_dec(x_179);
x_180 = !lean_is_exclusive(x_93);
if (x_180 == 0)
{
return x_92;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_93, 0);
x_182 = lean_ctor_get(x_93, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_93);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_92, 0, x_183);
return x_92;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_92, 1);
lean_inc(x_184);
lean_dec(x_92);
x_185 = lean_ctor_get(x_93, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_93, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_187 = x_93;
} else {
 lean_dec_ref(x_93);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_184);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_190 = !lean_is_exclusive(x_92);
if (x_190 == 0)
{
return x_92;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_92, 0);
x_192 = lean_ctor_get(x_92, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_92);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
block_47:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_array_get_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lake_LeanLib_recBuildLean___closed__4;
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_13, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lake_LeanLib_recBuildLean___closed__4;
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_8);
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = l_Lake_LeanLib_recBuildLean___closed__4;
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_11, x_21, x_22, x_23, x_2, x_3, x_4, x_5, x_12, x_9);
lean_dec(x_11);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lake_LeanLib_recBuildLean___closed__4;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_27, x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Lake_LeanLib_recBuildLean___closed__4;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = l_Lake_LeanLib_recBuildLean___closed__4;
x_40 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_25, x_37, x_38, x_39, x_2, x_3, x_4, x_5, x_26, x_9);
lean_dec(x_25);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
}
block_64:
{
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
lean_ctor_set(x_48, 1, x_52);
x_8 = x_48;
x_9 = x_49;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_8 = x_56;
x_9 = x_49;
goto block_47;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
lean_ctor_set(x_48, 1, x_59);
x_8 = x_48;
x_9 = x_49;
goto block_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_8 = x_63;
x_9 = x_49;
goto block_47;
}
}
}
block_89:
{
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 1);
x_69 = 0;
x_70 = l_Lake_BuildTrace_nil;
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_69);
lean_ctor_set(x_65, 1, x_71);
x_48 = x_65;
x_49 = x_66;
goto block_64;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = 0;
x_75 = l_Lake_BuildTrace_nil;
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_48 = x_77;
x_49 = x_66;
goto block_64;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 1);
x_80 = 0;
x_81 = l_Lake_BuildTrace_nil;
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_80);
lean_ctor_set(x_65, 1, x_82);
x_48 = x_65;
x_49 = x_66;
goto block_64;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_65, 0);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_65);
x_85 = 0;
x_86 = l_Lake_BuildTrace_nil;
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_48 = x_88;
x_49 = x_66;
goto block_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildLean), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_leanArtsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_leanArtsFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_apply_6(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(x_1);
x_16 = lean_apply_1(x_14, x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___rarg(x_2, x_11, x_17, x_18, x_16);
x_20 = lean_apply_6(x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = l_Array_append___rarg(x_3, x_25);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = l_Array_append___rarg(x_3, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_34 = x_21;
} else {
 lean_dec_ref(x_21);
 x_34 = lean_box(0);
}
x_35 = l_Array_append___rarg(x_3, x_32);
lean_dec(x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_20, 0, x_43);
return x_20;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_47 = x_21;
} else {
 lean_dec_ref(x_21);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_push(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__3___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_120; lean_object* x_121; lean_object* x_176; lean_object* x_177; lean_object* x_193; lean_object* x_194; lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_6, 0);
lean_inc(x_218);
lean_dec(x_6);
x_219 = lean_io_wait(x_218, x_12);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = !lean_is_exclusive(x_220);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_220, 0);
x_225 = lean_ctor_get(x_220, 1);
lean_dec(x_225);
x_226 = lean_ctor_get(x_221, 0);
lean_inc(x_226);
lean_dec(x_221);
x_227 = lean_array_get_size(x_226);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_nat_dec_lt(x_228, x_227);
if (x_229 == 0)
{
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_5);
lean_ctor_set(x_220, 1, x_11);
x_193 = x_220;
x_194 = x_222;
goto block_217;
}
else
{
uint8_t x_230; 
x_230 = lean_nat_dec_le(x_227, x_227);
if (x_230 == 0)
{
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_5);
lean_ctor_set(x_220, 1, x_11);
x_193 = x_220;
x_194 = x_222;
goto block_217;
}
else
{
size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_free_object(x_220);
x_231 = 0;
x_232 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_233 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_234 = lean_box(0);
x_235 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_233, x_226, x_231, x_232, x_234);
x_236 = lean_apply_2(x_235, x_11, x_222);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = !lean_is_exclusive(x_237);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_237, 0);
lean_dec(x_240);
lean_ctor_set(x_237, 0, x_224);
x_193 = x_237;
x_194 = x_238;
goto block_217;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_224);
lean_ctor_set(x_242, 1, x_241);
x_193 = x_242;
x_194 = x_238;
goto block_217;
}
}
else
{
lean_object* x_243; uint8_t x_244; 
lean_dec(x_224);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_dec(x_236);
x_244 = !lean_is_exclusive(x_237);
if (x_244 == 0)
{
x_193 = x_237;
x_194 = x_243;
goto block_217;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_237, 0);
x_246 = lean_ctor_get(x_237, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_237);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_193 = x_247;
x_194 = x_243;
goto block_217;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_224);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_236);
if (x_248 == 0)
{
return x_236;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_236, 0);
x_250 = lean_ctor_get(x_236, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_236);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_252 = lean_ctor_get(x_220, 0);
lean_inc(x_252);
lean_dec(x_220);
x_253 = lean_ctor_get(x_221, 0);
lean_inc(x_253);
lean_dec(x_221);
x_254 = lean_array_get_size(x_253);
x_255 = lean_unsigned_to_nat(0u);
x_256 = lean_nat_dec_lt(x_255, x_254);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_5);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_11);
x_193 = x_257;
x_194 = x_222;
goto block_217;
}
else
{
uint8_t x_258; 
x_258 = lean_nat_dec_le(x_254, x_254);
if (x_258 == 0)
{
lean_object* x_259; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_5);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_252);
lean_ctor_set(x_259, 1, x_11);
x_193 = x_259;
x_194 = x_222;
goto block_217;
}
else
{
size_t x_260; size_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = 0;
x_261 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_262 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_263 = lean_box(0);
x_264 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_262, x_253, x_260, x_261, x_263);
x_265 = lean_apply_2(x_264, x_11, x_222);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_252);
lean_ctor_set(x_270, 1, x_268);
x_193 = x_270;
x_194 = x_267;
goto block_217;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_252);
x_271 = lean_ctor_get(x_265, 1);
lean_inc(x_271);
lean_dec(x_265);
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_274 = x_266;
} else {
 lean_dec_ref(x_266);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
x_193 = x_275;
x_194 = x_271;
goto block_217;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_252);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_276 = lean_ctor_get(x_265, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_265, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_278 = x_265;
} else {
 lean_dec_ref(x_265);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = lean_ctor_get(x_220, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_219, 1);
lean_inc(x_281);
lean_dec(x_219);
x_282 = !lean_is_exclusive(x_220);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_283 = lean_ctor_get(x_220, 0);
x_284 = lean_ctor_get(x_220, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_280, 0);
lean_inc(x_285);
lean_dec(x_280);
x_286 = lean_array_get_size(x_285);
x_287 = lean_unsigned_to_nat(0u);
x_288 = lean_nat_dec_lt(x_287, x_286);
if (x_288 == 0)
{
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_5);
lean_ctor_set(x_220, 1, x_11);
x_193 = x_220;
x_194 = x_281;
goto block_217;
}
else
{
uint8_t x_289; 
x_289 = lean_nat_dec_le(x_286, x_286);
if (x_289 == 0)
{
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_5);
lean_ctor_set(x_220, 1, x_11);
x_193 = x_220;
x_194 = x_281;
goto block_217;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_free_object(x_220);
x_290 = 0;
x_291 = lean_usize_of_nat(x_286);
lean_dec(x_286);
x_292 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_293 = lean_box(0);
x_294 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_292, x_285, x_290, x_291, x_293);
x_295 = lean_apply_2(x_294, x_11, x_281);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = !lean_is_exclusive(x_296);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_296, 0);
lean_dec(x_299);
lean_ctor_set_tag(x_296, 1);
lean_ctor_set(x_296, 0, x_283);
x_193 = x_296;
x_194 = x_297;
goto block_217;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec(x_296);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_283);
lean_ctor_set(x_301, 1, x_300);
x_193 = x_301;
x_194 = x_297;
goto block_217;
}
}
else
{
lean_object* x_302; uint8_t x_303; 
lean_dec(x_283);
x_302 = lean_ctor_get(x_295, 1);
lean_inc(x_302);
lean_dec(x_295);
x_303 = !lean_is_exclusive(x_296);
if (x_303 == 0)
{
x_193 = x_296;
x_194 = x_302;
goto block_217;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_296, 0);
x_305 = lean_ctor_get(x_296, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_296);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_193 = x_306;
x_194 = x_302;
goto block_217;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_283);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_307 = !lean_is_exclusive(x_295);
if (x_307 == 0)
{
return x_295;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_295, 0);
x_309 = lean_ctor_get(x_295, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_295);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_220, 0);
lean_inc(x_311);
lean_dec(x_220);
x_312 = lean_ctor_get(x_280, 0);
lean_inc(x_312);
lean_dec(x_280);
x_313 = lean_array_get_size(x_312);
x_314 = lean_unsigned_to_nat(0u);
x_315 = lean_nat_dec_lt(x_314, x_313);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_5);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_311);
lean_ctor_set(x_316, 1, x_11);
x_193 = x_316;
x_194 = x_281;
goto block_217;
}
else
{
uint8_t x_317; 
x_317 = lean_nat_dec_le(x_313, x_313);
if (x_317 == 0)
{
lean_object* x_318; 
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_5);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_311);
lean_ctor_set(x_318, 1, x_11);
x_193 = x_318;
x_194 = x_281;
goto block_217;
}
else
{
size_t x_319; size_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_319 = 0;
x_320 = lean_usize_of_nat(x_313);
lean_dec(x_313);
x_321 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_322 = lean_box(0);
x_323 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_321, x_312, x_319, x_320, x_322);
x_324 = lean_apply_2(x_323, x_11, x_281);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
 lean_ctor_set_tag(x_329, 1);
}
lean_ctor_set(x_329, 0, x_311);
lean_ctor_set(x_329, 1, x_327);
x_193 = x_329;
x_194 = x_326;
goto block_217;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_311);
x_330 = lean_ctor_get(x_324, 1);
lean_inc(x_330);
lean_dec(x_324);
x_331 = lean_ctor_get(x_325, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_325, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_333 = x_325;
} else {
 lean_dec_ref(x_325);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
x_193 = x_334;
x_194 = x_330;
goto block_217;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_311);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_335 = lean_ctor_get(x_324, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_324, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_337 = x_324;
} else {
 lean_dec_ref(x_324);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_339 = !lean_is_exclusive(x_219);
if (x_339 == 0)
{
return x_219;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_219, 0);
x_341 = lean_ctor_get(x_219, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_219);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
block_119:
{
if (lean_obj_tag(x_13) == 0)
{
if (x_1 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 8);
lean_inc(x_21);
x_22 = l_System_FilePath_join(x_19, x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 10);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_System_FilePath_join(x_22, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_3, 5);
x_26 = l_Lake_nameToStaticLib(x_25);
x_27 = l_System_FilePath_join(x_24, x_26);
lean_dec(x_26);
x_28 = l_Lake_BuildTrace_nil;
x_29 = l_Lake_buildStaticLib(x_27, x_16, x_7, x_8, x_9, x_10, x_28, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_13, 0, x_31);
lean_ctor_set(x_29, 0, x_13);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_13, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_13);
lean_dec(x_17);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 8);
lean_inc(x_44);
x_45 = l_System_FilePath_join(x_42, x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 10);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_System_FilePath_join(x_45, x_46);
lean_dec(x_46);
x_48 = lean_ctor_get(x_3, 5);
x_49 = l_Lake_nameToStaticLib(x_48);
x_50 = l_System_FilePath_join(x_47, x_49);
lean_dec(x_49);
x_51 = l_Lake_BuildTrace_nil;
x_52 = l_Lake_buildStaticLib(x_50, x_39, x_7, x_8, x_9, x_10, x_51, x_14);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_40);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_40);
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_67, 8);
lean_inc(x_68);
x_69 = l_System_FilePath_join(x_66, x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_67, 10);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_System_FilePath_join(x_69, x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_3, 5);
x_73 = l_Lake_nameToStaticLib(x_72);
x_74 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_75 = l_System_FilePath_addExtension(x_73, x_74);
x_76 = l_System_FilePath_join(x_71, x_75);
lean_dec(x_75);
x_77 = l_Lake_BuildTrace_nil;
x_78 = l_Lake_buildStaticLib(x_76, x_63, x_7, x_8, x_9, x_10, x_77, x_14);
lean_dec(x_63);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_ctor_set(x_13, 0, x_80);
lean_ctor_set(x_78, 0, x_13);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_13, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_13);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_13);
lean_dec(x_64);
x_84 = !lean_is_exclusive(x_78);
if (x_84 == 0)
{
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_78, 0);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_78);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_13, 0);
x_89 = lean_ctor_get(x_13, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_13);
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
lean_dec(x_2);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 2);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_92, 8);
lean_inc(x_93);
x_94 = l_System_FilePath_join(x_91, x_93);
lean_dec(x_93);
x_95 = lean_ctor_get(x_92, 10);
lean_inc(x_95);
lean_dec(x_92);
x_96 = l_System_FilePath_join(x_94, x_95);
lean_dec(x_95);
x_97 = lean_ctor_get(x_3, 5);
x_98 = l_Lake_nameToStaticLib(x_97);
x_99 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_100 = l_System_FilePath_addExtension(x_98, x_99);
x_101 = l_System_FilePath_join(x_96, x_100);
lean_dec(x_100);
x_102 = l_Lake_BuildTrace_nil;
x_103 = l_Lake_buildStaticLib(x_101, x_88, x_7, x_8, x_9, x_10, x_102, x_14);
lean_dec(x_88);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_89);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_89);
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_111 = x_103;
} else {
 lean_dec_ref(x_103);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_13);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_13);
lean_ctor_set(x_114, 1, x_14);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_13, 0);
x_116 = lean_ctor_get(x_13, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_13);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_14);
return x_118;
}
}
}
block_175:
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
x_125 = l_Lake_EquipT_instMonad___rarg(x_4);
x_126 = lean_box(x_1);
lean_inc(x_125);
x_127 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__2___boxed), 10, 2);
lean_closure_set(x_127, 0, x_126);
lean_closure_set(x_127, 1, x_125);
x_128 = lean_array_get_size(x_123);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_nat_dec_lt(x_129, x_128);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_123);
x_131 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_120, 0, x_131);
x_13 = x_120;
x_14 = x_121;
goto block_119;
}
else
{
uint8_t x_132; 
x_132 = lean_nat_dec_le(x_128, x_128);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_123);
x_133 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_120, 0, x_133);
x_13 = x_120;
x_14 = x_121;
goto block_119;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_free_object(x_120);
x_134 = 0;
x_135 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_136 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_137 = l_Array_foldlMUnsafe_fold___rarg(x_125, x_127, x_123, x_134, x_135, x_136);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_138 = lean_apply_6(x_137, x_7, x_8, x_9, x_10, x_124, x_121);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_13 = x_139;
x_14 = x_140;
goto block_119;
}
else
{
uint8_t x_141; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_145 = lean_ctor_get(x_120, 0);
x_146 = lean_ctor_get(x_120, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_120);
x_147 = l_Lake_EquipT_instMonad___rarg(x_4);
x_148 = lean_box(x_1);
lean_inc(x_147);
x_149 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__2___boxed), 10, 2);
lean_closure_set(x_149, 0, x_148);
lean_closure_set(x_149, 1, x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_nat_dec_lt(x_151, x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
x_153 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
x_13 = x_154;
x_14 = x_121;
goto block_119;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_150, x_150);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
x_156 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_146);
x_13 = x_157;
x_14 = x_121;
goto block_119;
}
else
{
size_t x_158; size_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = 0;
x_159 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_160 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_161 = l_Array_foldlMUnsafe_fold___rarg(x_147, x_149, x_145, x_158, x_159, x_160);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_162 = lean_apply_6(x_161, x_7, x_8, x_9, x_10, x_146, x_121);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_13 = x_163;
x_14 = x_164;
goto block_119;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_120);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_120);
lean_ctor_set(x_170, 1, x_121);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_120, 0);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_120);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_121);
return x_174;
}
}
}
block_192:
{
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_176, 1);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
lean_ctor_set(x_176, 1, x_180);
x_120 = x_176;
x_121 = x_177;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_176, 0);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_176);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
x_120 = x_184;
x_121 = x_177;
goto block_175;
}
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_176);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_176, 1);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec(x_186);
lean_ctor_set(x_176, 1, x_187);
x_120 = x_176;
x_121 = x_177;
goto block_175;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_176, 0);
x_189 = lean_ctor_get(x_176, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_176);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_120 = x_191;
x_121 = x_177;
goto block_175;
}
}
}
block_217:
{
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_193, 1);
x_197 = 0;
x_198 = l_Lake_BuildTrace_nil;
x_199 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_197);
lean_ctor_set(x_193, 1, x_199);
x_176 = x_193;
x_177 = x_194;
goto block_192;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_193, 0);
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_193);
x_202 = 0;
x_203 = l_Lake_BuildTrace_nil;
x_204 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_202);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_200);
lean_ctor_set(x_205, 1, x_204);
x_176 = x_205;
x_177 = x_194;
goto block_192;
}
}
else
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_193);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_193, 1);
x_208 = 0;
x_209 = l_Lake_BuildTrace_nil;
x_210 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_208);
lean_ctor_set(x_193, 1, x_210);
x_176 = x_193;
x_177 = x_194;
goto block_192;
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_193, 0);
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_193);
x_213 = 0;
x_214 = l_Lake_BuildTrace_nil;
x_215 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_213);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_215);
x_176 = x_216;
x_177 = x_194;
goto block_192;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadBaseIO;
x_2 = l_Lake_EStateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":static", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (without exports)", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (with exports)", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 3);
lean_dec(x_11);
x_13 = 2;
x_14 = l_Lake_instDecidableEqVerbosity(x_12, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = 1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1;
x_19 = l_Lean_Name_toString(x_16, x_17, x_18);
x_20 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lake_LeanLib_recBuildStatic___closed__5;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
lean_inc(x_1);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, lean_box(0));
x_27 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_28 = lean_box(x_2);
x_29 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__4___boxed), 12, 5);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_15);
lean_closure_set(x_29, 3, x_9);
lean_closure_set(x_29, 4, x_27);
x_30 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___rarg), 6, 5);
lean_closure_set(x_30, 0, x_10);
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, lean_box(0));
lean_closure_set(x_30, 3, x_26);
lean_closure_set(x_30, 4, x_29);
if (x_14 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_string_append(x_23, x_20);
x_32 = lean_string_append(x_31, x_20);
x_33 = 0;
x_34 = l_Lake_withRegisterJob___rarg(x_32, x_30, x_33, x_3, x_4, x_5, x_6, x_7, x_8);
return x_34;
}
else
{
if (x_2 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_35 = l_Lake_LeanLib_recBuildStatic___closed__6;
x_36 = lean_string_append(x_23, x_35);
x_37 = lean_string_append(x_36, x_20);
x_38 = 0;
x_39 = l_Lake_withRegisterJob___rarg(x_37, x_30, x_38, x_3, x_4, x_5, x_6, x_7, x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = l_Lake_LeanLib_recBuildStatic___closed__7;
x_41 = lean_string_append(x_23, x_40);
x_42 = lean_string_append(x_41, x_20);
x_43 = 0;
x_44 = l_Lake_withRegisterJob___rarg(x_42, x_30, x_43, x_3, x_4, x_5, x_6, x_7, x_8);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lake_LeanLib_recBuildStatic___lambda__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_LeanLib_recBuildStatic___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lake_LeanLib_recBuildStatic___lambda__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_LeanLib_recBuildStatic(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lake_LeanLib_recBuildStatic(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_staticFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_staticFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_LeanLib_staticFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_staticFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_staticFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lake_LeanLib_recBuildStatic(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLib_staticFacetConfig___closed__1;
x_2 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticExportFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticExportFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_staticExportFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_LeanLib_staticExportFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_staticExportFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_staticExportFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_8, 2);
x_10 = lean_name_eq(x_7, x_9);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recBuildShared___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recBuildShared___spec__5___at_Lake_LeanLib_recBuildShared___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
lean_ctor_set(x_2, 2, x_21);
x_22 = lean_array_uset(x_1, x_20, x_2);
x_1 = x_22;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_27 = lean_array_get_size(x_1);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Name_hash___override(x_29);
lean_dec(x_29);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_1, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_uset(x_1, x_41, x_43);
x_1 = x_44;
x_2 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recBuildShared___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recBuildShared___spec__5___at_Lake_LeanLib_recBuildShared___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recBuildShared___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recBuildShared___spec__4(x_7, x_1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Name_hash___override(x_9);
lean_dec(x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_6, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_6, x_21, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_27, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recBuildShared___spec__3(x_30);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
else
{
lean_object* x_39; 
lean_ctor_set(x_3, 1, x_30);
lean_ctor_set(x_3, 0, x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = lean_array_get_size(x_41);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Name_hash___override(x_44);
lean_dec(x_44);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_41, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2(x_2, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
lean_inc(x_2);
x_60 = lean_array_push(x_59, x_2);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_40, x_61);
lean_dec(x_40);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_57);
x_65 = lean_array_uset(x_41, x_56, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_62, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recBuildShared___spec__3(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_65);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
}
else
{
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_1, x_2, x_4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
x_10 = lean_array_push(x_8, x_9);
x_2 = x_10;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_13);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_apply_6(x_4, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_23;
x_3 = x_24;
x_8 = x_21;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 10);
lean_inc(x_13);
x_14 = 0;
x_15 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_16 = l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_12, x_15, x_13);
lean_dec(x_13);
x_17 = lean_array_size(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8(x_17, x_14, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Array_append___rarg(x_4, x_21);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1(x_4, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_apply_6(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 8);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_apply_1(x_15, x_17);
x_19 = lean_array_size(x_18);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11(x_12, x_19, x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Array_append___rarg(x_4, x_24);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_26;
x_9 = x_25;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_39 = x_22;
} else {
 lean_dec_ref(x_22);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_9);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_256; lean_object* x_257; lean_object* x_273; lean_object* x_274; lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_3, 0);
lean_inc(x_298);
lean_dec(x_3);
x_299 = lean_io_wait(x_298, x_9);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = !lean_is_exclusive(x_300);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_304 = lean_ctor_get(x_300, 0);
x_305 = lean_ctor_get(x_300, 1);
lean_dec(x_305);
x_306 = lean_ctor_get(x_301, 0);
lean_inc(x_306);
lean_dec(x_301);
x_307 = lean_array_get_size(x_306);
x_308 = lean_unsigned_to_nat(0u);
x_309 = lean_nat_dec_lt(x_308, x_307);
if (x_309 == 0)
{
lean_dec(x_307);
lean_dec(x_306);
lean_ctor_set(x_300, 1, x_8);
x_273 = x_300;
x_274 = x_302;
goto block_297;
}
else
{
uint8_t x_310; 
x_310 = lean_nat_dec_le(x_307, x_307);
if (x_310 == 0)
{
lean_dec(x_307);
lean_dec(x_306);
lean_ctor_set(x_300, 1, x_8);
x_273 = x_300;
x_274 = x_302;
goto block_297;
}
else
{
size_t x_311; size_t x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_free_object(x_300);
x_311 = 0;
x_312 = lean_usize_of_nat(x_307);
lean_dec(x_307);
x_313 = lean_box(0);
x_314 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_306, x_311, x_312, x_313, x_8, x_302);
lean_dec(x_306);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = !lean_is_exclusive(x_315);
if (x_317 == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_315, 0);
lean_dec(x_318);
lean_ctor_set(x_315, 0, x_304);
x_273 = x_315;
x_274 = x_316;
goto block_297;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
lean_dec(x_315);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_304);
lean_ctor_set(x_320, 1, x_319);
x_273 = x_320;
x_274 = x_316;
goto block_297;
}
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_321 = lean_ctor_get(x_300, 0);
lean_inc(x_321);
lean_dec(x_300);
x_322 = lean_ctor_get(x_301, 0);
lean_inc(x_322);
lean_dec(x_301);
x_323 = lean_array_get_size(x_322);
x_324 = lean_unsigned_to_nat(0u);
x_325 = lean_nat_dec_lt(x_324, x_323);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_323);
lean_dec(x_322);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_8);
x_273 = x_326;
x_274 = x_302;
goto block_297;
}
else
{
uint8_t x_327; 
x_327 = lean_nat_dec_le(x_323, x_323);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_323);
lean_dec(x_322);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_8);
x_273 = x_328;
x_274 = x_302;
goto block_297;
}
else
{
size_t x_329; size_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_329 = 0;
x_330 = lean_usize_of_nat(x_323);
lean_dec(x_323);
x_331 = lean_box(0);
x_332 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_322, x_329, x_330, x_331, x_8, x_302);
lean_dec(x_322);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_321);
lean_ctor_set(x_337, 1, x_335);
x_273 = x_337;
x_274 = x_334;
goto block_297;
}
}
}
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_ctor_get(x_300, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_299, 1);
lean_inc(x_339);
lean_dec(x_299);
x_340 = !lean_is_exclusive(x_300);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_341 = lean_ctor_get(x_300, 0);
x_342 = lean_ctor_get(x_300, 1);
lean_dec(x_342);
x_343 = lean_ctor_get(x_338, 0);
lean_inc(x_343);
lean_dec(x_338);
x_344 = lean_array_get_size(x_343);
x_345 = lean_unsigned_to_nat(0u);
x_346 = lean_nat_dec_lt(x_345, x_344);
if (x_346 == 0)
{
lean_dec(x_344);
lean_dec(x_343);
lean_ctor_set(x_300, 1, x_8);
x_273 = x_300;
x_274 = x_339;
goto block_297;
}
else
{
uint8_t x_347; 
x_347 = lean_nat_dec_le(x_344, x_344);
if (x_347 == 0)
{
lean_dec(x_344);
lean_dec(x_343);
lean_ctor_set(x_300, 1, x_8);
x_273 = x_300;
x_274 = x_339;
goto block_297;
}
else
{
size_t x_348; size_t x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
lean_free_object(x_300);
x_348 = 0;
x_349 = lean_usize_of_nat(x_344);
lean_dec(x_344);
x_350 = lean_box(0);
x_351 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_343, x_348, x_349, x_350, x_8, x_339);
lean_dec(x_343);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_352, 0);
lean_dec(x_355);
lean_ctor_set_tag(x_352, 1);
lean_ctor_set(x_352, 0, x_341);
x_273 = x_352;
x_274 = x_353;
goto block_297;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_341);
lean_ctor_set(x_357, 1, x_356);
x_273 = x_357;
x_274 = x_353;
goto block_297;
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_358 = lean_ctor_get(x_300, 0);
lean_inc(x_358);
lean_dec(x_300);
x_359 = lean_ctor_get(x_338, 0);
lean_inc(x_359);
lean_dec(x_338);
x_360 = lean_array_get_size(x_359);
x_361 = lean_unsigned_to_nat(0u);
x_362 = lean_nat_dec_lt(x_361, x_360);
if (x_362 == 0)
{
lean_object* x_363; 
lean_dec(x_360);
lean_dec(x_359);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_358);
lean_ctor_set(x_363, 1, x_8);
x_273 = x_363;
x_274 = x_339;
goto block_297;
}
else
{
uint8_t x_364; 
x_364 = lean_nat_dec_le(x_360, x_360);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_360);
lean_dec(x_359);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_8);
x_273 = x_365;
x_274 = x_339;
goto block_297;
}
else
{
size_t x_366; size_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_366 = 0;
x_367 = lean_usize_of_nat(x_360);
lean_dec(x_360);
x_368 = lean_box(0);
x_369 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_359, x_366, x_367, x_368, x_8, x_339);
lean_dec(x_359);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
 lean_ctor_set_tag(x_374, 1);
}
lean_ctor_set(x_374, 0, x_358);
lean_ctor_set(x_374, 1, x_372);
x_273 = x_374;
x_274 = x_371;
goto block_297;
}
}
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_375 = !lean_is_exclusive(x_299);
if (x_375 == 0)
{
return x_299;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_299, 0);
x_377 = lean_ctor_get(x_299, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_299);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
block_255:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_131 = lean_array_get_size(x_13);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_lt(x_132, x_131);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
x_134 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_10, 0, x_134);
x_15 = x_10;
x_16 = x_11;
goto block_130;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_le(x_131, x_131);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_131);
x_136 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_10, 0, x_136);
x_15 = x_10;
x_16 = x_11;
goto block_130;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_10);
x_137 = 0;
x_138 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_139 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_140 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12(x_13, x_137, x_138, x_139, x_4, x_5, x_6, x_7, x_14, x_11);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_15 = x_141;
x_16 = x_142;
goto block_130;
}
else
{
uint8_t x_143; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_140);
if (x_143 == 0)
{
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
block_130:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_94 = lean_array_get_size(x_13);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_94);
if (x_96 == 0)
{
lean_object* x_117; 
lean_dec(x_94);
lean_dec(x_13);
x_117 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_97 = x_117;
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_94, x_94);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_94);
lean_dec(x_13);
x_119 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_97 = x_119;
goto block_116;
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_122 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_123 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(x_13, x_120, x_121, x_122);
lean_dec(x_13);
x_97 = x_123;
goto block_116;
}
}
block_93:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 8);
lean_inc(x_28);
x_29 = l_System_FilePath_join(x_26, x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_27, 10);
lean_inc(x_30);
x_31 = l_System_FilePath_join(x_29, x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_2, 5);
x_33 = l_Lake_nameToSharedLib(x_32);
x_34 = l_System_FilePath_join(x_31, x_33);
lean_dec(x_33);
x_35 = l_Array_append___rarg(x_17, x_23);
lean_dec(x_23);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_36, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_38, 7);
x_40 = l_Array_append___rarg(x_37, x_39);
x_41 = lean_ctor_get(x_36, 6);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_ctor_get(x_38, 6);
x_43 = l_Array_append___rarg(x_41, x_42);
x_44 = l_Lake_BuildTrace_nil;
x_45 = l_Lake_buildLeanSharedLib(x_34, x_35, x_40, x_43, x_4, x_5, x_6, x_7, x_44, x_21);
lean_dec(x_35);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_20, 0, x_47);
lean_ctor_set(x_45, 0, x_20);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_20, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_20);
lean_dec(x_24);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 2);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_59, 8);
lean_inc(x_60);
x_61 = l_System_FilePath_join(x_58, x_60);
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 10);
lean_inc(x_62);
x_63 = l_System_FilePath_join(x_61, x_62);
lean_dec(x_62);
x_64 = lean_ctor_get(x_2, 5);
x_65 = l_Lake_nameToSharedLib(x_64);
x_66 = l_System_FilePath_join(x_63, x_65);
lean_dec(x_65);
x_67 = l_Array_append___rarg(x_17, x_55);
lean_dec(x_55);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_ctor_get(x_68, 7);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_70, 7);
x_72 = l_Array_append___rarg(x_69, x_71);
x_73 = lean_ctor_get(x_68, 6);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_ctor_get(x_70, 6);
x_75 = l_Array_append___rarg(x_73, x_74);
x_76 = l_Lake_BuildTrace_nil;
x_77 = l_Lake_buildLeanSharedLib(x_66, x_67, x_72, x_75, x_4, x_5, x_6, x_7, x_76, x_21);
lean_dec(x_67);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_56);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_56);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_20);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_20);
lean_ctor_set(x_88, 1, x_21);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_20, 0);
x_90 = lean_ctor_get(x_20, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_20);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_21);
return x_92;
}
}
}
block_116:
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_array_get_size(x_98);
x_100 = lean_nat_dec_lt(x_95, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_99);
lean_dec(x_98);
x_101 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
if (lean_is_scalar(x_19)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_19;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_18);
x_20 = x_102;
x_21 = x_16;
goto block_93;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_99, x_99);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_98);
x_104 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
if (lean_is_scalar(x_19)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_19;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_18);
x_20 = x_105;
x_21 = x_16;
goto block_93;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_19);
x_106 = 0;
x_107 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_108 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_109 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9(x_98, x_106, x_107, x_108, x_4, x_5, x_6, x_7, x_18, x_16);
lean_dec(x_98);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_20 = x_110;
x_21 = x_111;
goto block_93;
}
else
{
uint8_t x_112; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_15);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_15);
lean_ctor_set(x_125, 1, x_16);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_15, 0);
x_127 = lean_ctor_get(x_15, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_15);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_16);
return x_129;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_147 = lean_ctor_get(x_10, 0);
x_148 = lean_ctor_get(x_10, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_10);
x_231 = lean_array_get_size(x_147);
x_232 = lean_unsigned_to_nat(0u);
x_233 = lean_nat_dec_lt(x_232, x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
x_234 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_148);
x_149 = x_235;
x_150 = x_11;
goto block_230;
}
else
{
uint8_t x_236; 
x_236 = lean_nat_dec_le(x_231, x_231);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_231);
x_237 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_148);
x_149 = x_238;
x_150 = x_11;
goto block_230;
}
else
{
size_t x_239; size_t x_240; lean_object* x_241; lean_object* x_242; 
x_239 = 0;
x_240 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_241 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_242 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12(x_147, x_239, x_240, x_241, x_4, x_5, x_6, x_7, x_148, x_11);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_149 = x_243;
x_150 = x_244;
goto block_230;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
block_230:
{
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_195 = lean_array_get_size(x_147);
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_nat_dec_lt(x_196, x_195);
if (x_197 == 0)
{
lean_object* x_218; 
lean_dec(x_195);
lean_dec(x_147);
x_218 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_198 = x_218;
goto block_217;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_195, x_195);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_195);
lean_dec(x_147);
x_220 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_198 = x_220;
goto block_217;
}
else
{
size_t x_221; size_t x_222; lean_object* x_223; lean_object* x_224; 
x_221 = 0;
x_222 = lean_usize_of_nat(x_195);
lean_dec(x_195);
x_223 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_224 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(x_147, x_221, x_222, x_223);
lean_dec(x_147);
x_198 = x_224;
goto block_217;
}
}
block_194:
{
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_158 = x_154;
} else {
 lean_dec_ref(x_154);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
lean_dec(x_1);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 2);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_161, 8);
lean_inc(x_162);
x_163 = l_System_FilePath_join(x_160, x_162);
lean_dec(x_162);
x_164 = lean_ctor_get(x_161, 10);
lean_inc(x_164);
x_165 = l_System_FilePath_join(x_163, x_164);
lean_dec(x_164);
x_166 = lean_ctor_get(x_2, 5);
x_167 = l_Lake_nameToSharedLib(x_166);
x_168 = l_System_FilePath_join(x_165, x_167);
lean_dec(x_167);
x_169 = l_Array_append___rarg(x_151, x_156);
lean_dec(x_156);
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
lean_dec(x_161);
x_171 = lean_ctor_get(x_170, 7);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 0);
x_173 = lean_ctor_get(x_172, 7);
x_174 = l_Array_append___rarg(x_171, x_173);
x_175 = lean_ctor_get(x_170, 6);
lean_inc(x_175);
lean_dec(x_170);
x_176 = lean_ctor_get(x_172, 6);
x_177 = l_Array_append___rarg(x_175, x_176);
x_178 = l_Lake_BuildTrace_nil;
x_179 = l_Lake_buildLeanSharedLib(x_168, x_169, x_174, x_177, x_4, x_5, x_6, x_7, x_178, x_155);
lean_dec(x_169);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_158;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_157);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_158);
lean_dec(x_157);
x_185 = lean_ctor_get(x_179, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_187 = x_179;
} else {
 lean_dec_ref(x_179);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_151);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_189 = lean_ctor_get(x_154, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_154, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_191 = x_154;
} else {
 lean_dec_ref(x_154);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_155);
return x_193;
}
}
block_217:
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_array_get_size(x_199);
x_201 = lean_nat_dec_lt(x_196, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_200);
lean_dec(x_199);
x_202 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
if (lean_is_scalar(x_153)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_153;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_152);
x_154 = x_203;
x_155 = x_150;
goto block_194;
}
else
{
uint8_t x_204; 
x_204 = lean_nat_dec_le(x_200, x_200);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_200);
lean_dec(x_199);
x_205 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
if (lean_is_scalar(x_153)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_153;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_152);
x_154 = x_206;
x_155 = x_150;
goto block_194;
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_153);
x_207 = 0;
x_208 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_209 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_210 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9(x_199, x_207, x_208, x_209, x_4, x_5, x_6, x_7, x_152, x_150);
lean_dec(x_199);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_154 = x_211;
x_155 = x_212;
goto block_194;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_151);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_225 = lean_ctor_get(x_149, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_149, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_227 = x_149;
} else {
 lean_dec_ref(x_149);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_150);
return x_229;
}
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_10);
if (x_249 == 0)
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_10);
lean_ctor_set(x_250, 1, x_11);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_10, 0);
x_252 = lean_ctor_get(x_10, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_10);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_11);
return x_254;
}
}
}
block_272:
{
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_256, 1);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec(x_259);
lean_ctor_set(x_256, 1, x_260);
x_10 = x_256;
x_11 = x_257;
goto block_255;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_256, 0);
x_262 = lean_ctor_get(x_256, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_256);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_263);
x_10 = x_264;
x_11 = x_257;
goto block_255;
}
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_256);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_256, 1);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec(x_266);
lean_ctor_set(x_256, 1, x_267);
x_10 = x_256;
x_11 = x_257;
goto block_255;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_256, 0);
x_269 = lean_ctor_get(x_256, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_256);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_270);
x_10 = x_271;
x_11 = x_257;
goto block_255;
}
}
}
block_297:
{
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_273, 1);
x_277 = 0;
x_278 = l_Lake_BuildTrace_nil;
x_279 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set_uint8(x_279, sizeof(void*)*2, x_277);
lean_ctor_set(x_273, 1, x_279);
x_256 = x_273;
x_257 = x_274;
goto block_272;
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_280 = lean_ctor_get(x_273, 0);
x_281 = lean_ctor_get(x_273, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_273);
x_282 = 0;
x_283 = l_Lake_BuildTrace_nil;
x_284 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set_uint8(x_284, sizeof(void*)*2, x_282);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_284);
x_256 = x_285;
x_257 = x_274;
goto block_272;
}
}
else
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_273);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_273, 1);
x_288 = 0;
x_289 = l_Lake_BuildTrace_nil;
x_290 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*2, x_288);
lean_ctor_set(x_273, 1, x_290);
x_256 = x_273;
x_257 = x_274;
goto block_272;
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_291 = lean_ctor_get(x_273, 0);
x_292 = lean_ctor_get(x_273, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_273);
x_293 = 0;
x_294 = l_Lake_BuildTrace_nil;
x_295 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set_uint8(x_295, sizeof(void*)*2, x_293);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_291);
lean_ctor_set(x_296, 1, x_295);
x_256 = x_296;
x_257 = x_274;
goto block_272;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildShared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":shared", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_LeanLib_recBuildShared___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
lean_inc(x_1);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, lean_box(0));
x_20 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared___lambda__1___boxed), 9, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_8);
x_21 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = 0;
x_23 = l_Lake_withRegisterJob___rarg(x_16, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recBuildShared___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__8(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__9(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__12(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_LeanLib_recBuildShared___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_sharedFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_sharedFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_sharedFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_LeanLib_sharedFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_sharedFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_sharedFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lake_Package_fetchTargetJob(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lake_Job_mix___rarg(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_10);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extraDep", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__2;
lean_inc(x_9);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_11);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_10, 6);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_free_object(x_13);
lean_free_object(x_12);
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_9, x_20, x_25, x_26, x_18, x_2, x_3, x_4, x_5, x_19, x_15);
lean_dec(x_20);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_ctor_get(x_10, 6);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_free_object(x_12);
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_9, x_30, x_37, x_38, x_28, x_2, x_3, x_4, x_5, x_29, x_15);
lean_dec(x_30);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_43 = x_13;
} else {
 lean_dec_ref(x_13);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_10, 6);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_array_get_size(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
lean_dec(x_43);
x_53 = 0;
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_9, x_44, x_53, x_54, x_41, x_2, x_3, x_4, x_5, x_42, x_40);
lean_dec(x_44);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_12, 0, x_61);
return x_12;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
lean_dec(x_12);
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_12);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
x_74 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__2;
lean_inc(x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = lean_apply_6(x_2, x_75, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_73, 6);
lean_inc(x_83);
lean_dec(x_73);
x_84 = lean_array_get_size(x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_84, x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_81);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_79;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_78);
return x_91;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_79);
x_92 = 0;
x_93 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_94 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_72, x_83, x_92, x_93, x_80, x_2, x_3, x_4, x_5, x_81, x_78);
lean_dec(x_83);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_96 = x_76;
} else {
 lean_dec_ref(x_76);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_99 = x_77;
} else {
 lean_dec_ref(x_77);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
if (lean_is_scalar(x_96)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_96;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_95);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_76, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_104 = x_76;
} else {
 lean_dec_ref(x_76);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_extraDepFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_extraDepFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_LeanLib_extraDepFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_extraDepFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_extraDepFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_3 = l_Lake_LeanLib_modulesFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2;
x_3 = l_Lake_LeanLib_leanArtsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__2;
x_2 = l_Lake_LeanLib_staticFacetConfig___closed__2;
x_3 = l_Lake_LeanLib_staticFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__3;
x_2 = l_Lake_LeanLib_staticExportFacetConfig___closed__1;
x_3 = l_Lake_LeanLib_staticExportFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__4;
x_2 = l_Lake_LeanLib_sharedFacetConfig___closed__2;
x_3 = l_Lake_LeanLib_sharedFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__5;
x_2 = l_Lake_LeanLib_recBuildExtraDepTargets___closed__2;
x_3 = l_Lake_LeanLib_extraDepFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addLibraryFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initLibraryFacetConfigs___closed__6;
return x_1;
}
}
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanLib_recCollectLocalModules_go___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules_go___closed__1);
l_Lake_LeanLib_recCollectLocalModules_go___closed__2 = _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules_go___closed__2);
l_Lake_LeanLib_recCollectLocalModules_go___closed__3 = _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules_go___closed__3);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__4);
l_Lake_LeanLib_recCollectLocalModules___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__2___closed__2);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__1);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__2);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__3);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__4);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__5);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___elambda__1___spec__1___closed__6);
l_Lake_LeanLib_modulesFacetConfig___closed__1 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__1);
l_Lake_LeanLib_modulesFacetConfig___closed__2 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__2);
l_Lake_LeanLib_modulesFacetConfig___closed__3 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__3);
l_Lake_LeanLib_modulesFacetConfig___closed__4 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__4();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__4);
l_Lake_LeanLib_modulesFacetConfig___closed__5 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__5();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__5);
l_Lake_LeanLib_modulesFacetConfig = _init_l_Lake_LeanLib_modulesFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___closed__2);
l_Lake_LeanLib_recBuildLean___closed__1 = _init_l_Lake_LeanLib_recBuildLean___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__1);
l_Lake_LeanLib_recBuildLean___closed__2 = _init_l_Lake_LeanLib_recBuildLean___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__2);
l_Lake_LeanLib_recBuildLean___closed__3 = _init_l_Lake_LeanLib_recBuildLean___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__3);
l_Lake_LeanLib_recBuildLean___closed__4 = _init_l_Lake_LeanLib_recBuildLean___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__4);
l_Lake_LeanLib_leanArtsFacetConfig___closed__1 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
l_Lake_LeanLib_leanArtsFacetConfig___closed__2 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
l_Lake_LeanLib_leanArtsFacetConfig___closed__3 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__3);
l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3);
l_Lake_LeanLib_recBuildStatic___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__1);
l_Lake_LeanLib_recBuildStatic___closed__2 = _init_l_Lake_LeanLib_recBuildStatic___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__2);
l_Lake_LeanLib_recBuildStatic___closed__3 = _init_l_Lake_LeanLib_recBuildStatic___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__3);
l_Lake_LeanLib_recBuildStatic___closed__4 = _init_l_Lake_LeanLib_recBuildStatic___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__4);
l_Lake_LeanLib_recBuildStatic___closed__5 = _init_l_Lake_LeanLib_recBuildStatic___closed__5();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__5);
l_Lake_LeanLib_recBuildStatic___closed__6 = _init_l_Lake_LeanLib_recBuildStatic___closed__6();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__6);
l_Lake_LeanLib_recBuildStatic___closed__7 = _init_l_Lake_LeanLib_recBuildStatic___closed__7();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__7);
l_Lake_LeanLib_staticFacetConfig___closed__1 = _init_l_Lake_LeanLib_staticFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__1);
l_Lake_LeanLib_staticFacetConfig___closed__2 = _init_l_Lake_LeanLib_staticFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__2);
l_Lake_LeanLib_staticFacetConfig___closed__3 = _init_l_Lake_LeanLib_staticFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__3);
l_Lake_LeanLib_staticFacetConfig___closed__4 = _init_l_Lake_LeanLib_staticFacetConfig___closed__4();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__4);
l_Lake_LeanLib_staticFacetConfig___closed__5 = _init_l_Lake_LeanLib_staticFacetConfig___closed__5();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__5);
l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
l_Lake_LeanLib_staticExportFacetConfig___closed__1 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__1);
l_Lake_LeanLib_staticExportFacetConfig___closed__2 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__2);
l_Lake_LeanLib_staticExportFacetConfig___closed__3 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__3);
l_Lake_LeanLib_staticExportFacetConfig___closed__4 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__4();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__4);
l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__1___closed__2);
l_Lake_LeanLib_recBuildShared___closed__1 = _init_l_Lake_LeanLib_recBuildShared___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildShared___closed__1);
l_Lake_LeanLib_sharedFacetConfig___closed__1 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__1);
l_Lake_LeanLib_sharedFacetConfig___closed__2 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__2);
l_Lake_LeanLib_sharedFacetConfig___closed__3 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__3);
l_Lake_LeanLib_sharedFacetConfig___closed__4 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__4();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__4);
l_Lake_LeanLib_sharedFacetConfig___closed__5 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__5();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__5);
l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
l_Lake_LeanLib_recBuildExtraDepTargets___closed__1 = _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildExtraDepTargets___closed__1);
l_Lake_LeanLib_recBuildExtraDepTargets___closed__2 = _init_l_Lake_LeanLib_recBuildExtraDepTargets___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildExtraDepTargets___closed__2);
l_Lake_LeanLib_extraDepFacetConfig___closed__1 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__1);
l_Lake_LeanLib_extraDepFacetConfig___closed__2 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__2);
l_Lake_LeanLib_extraDepFacetConfig___closed__3 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__3);
l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
l_Lake_initLibraryFacetConfigs___closed__1 = _init_l_Lake_initLibraryFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__1);
l_Lake_initLibraryFacetConfigs___closed__2 = _init_l_Lake_initLibraryFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__2);
l_Lake_initLibraryFacetConfigs___closed__3 = _init_l_Lake_initLibraryFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__3);
l_Lake_initLibraryFacetConfigs___closed__4 = _init_l_Lake_initLibraryFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__4);
l_Lake_initLibraryFacetConfigs___closed__5 = _init_l_Lake_initLibraryFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__5);
l_Lake_initLibraryFacetConfigs___closed__6 = _init_l_Lake_initLibraryFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs___closed__6);
l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
