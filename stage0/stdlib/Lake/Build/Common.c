// Lean compiler output
// Module: Lake.Build.Common
// Imports: public import Lake.Build.Job.Monad public import Lake.Config.Monad public import Lake.Util.JsonObject public import Lake.Util.IO public import Lake.Build.Actions
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_System_Platform_target;
uint64_t lean_string_hash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_Lake_writeBinFileIfNew(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__0 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__0_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__1 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__2 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__3 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__4 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__5 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__6 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__0_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__7 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__8 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__9 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__0, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__10 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__11 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__12 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__13 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__13_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__16 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__16_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EStateT_instPure___redArg___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__16_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__17 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
static lean_once_cell_t l_Lake_platformTrace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__0;
static lean_once_cell_t l_Lake_platformTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__1;
static const lean_array_object l_Lake_platformTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_platformTrace___closed__2 = (const lean_object*)&l_Lake_platformTrace___closed__2_value;
static lean_once_cell_t l_Lake_platformTrace___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__3;
static lean_once_cell_t l_Lake_platformTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__4;
static lean_once_cell_t l_Lake_platformTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_addPureTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_addPureTrace___redArg___closed__0 = (const lean_object*)&l_Lake_addPureTrace___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-09-10"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__0_value;
static const lean_ctor_object l_Lake_BuildMetadata_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__1_value;
static lean_once_cell_t l_Lake_BuildMetadata_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_toJson___closed__2;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depHash"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__3_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "log"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__6_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "synthetic"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object*);
static const lean_closure_object l_Lake_instToJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonBuildMetadata = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_ofStub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_ofStub___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_ofStub___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value;
static const lean_string_object l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1 = (const lean_object*)&l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "synthetic: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "log: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "outputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value;
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: depHash"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "depHash: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid trace: expected string 'depHash' of decimal digits"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid trace stub: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown trace format: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid trace: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "unknown trace format: expected JSON number or object"};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object*);
static const lean_closure_object l_Lake_instFromJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_fromJson_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonBuildMetadata = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_readTraceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": read failed: "};
static const lean_object* l_Lake_readTraceFile___closed__0 = (const lean_object*)&l_Lake_readTraceFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object*);
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonPUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonPUnit___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonPUnit = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
static const lean_string_object l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instToOutputJsonArtifact___lam__0___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonArtifact___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonArtifact___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonArtifact = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "target is out-of-date and needs to be rebuilt"};
static const lean_object* l_Lake_buildAction___redArg___closed__0 = (const lean_object*)&l_Lake_buildAction___redArg___closed__0_value;
static const lean_ctor_object l_Lake_buildAction___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_buildAction___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_buildAction___redArg___closed__1 = (const lean_object*)&l_Lake_buildAction___redArg___closed__1_value;
static const lean_string_object l_Lake_buildAction___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nobuild"};
static const lean_object* l_Lake_buildAction___redArg___closed__2 = (const lean_object*)&l_Lake_buildAction___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_writeFileHash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".hash"};
static const lean_object* l_Lake_writeFileHash___closed__0 = (const lean_object*)&l_Lake_writeFileHash___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileUnlessUpToDate_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".trace"};
static const lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0 = (const lean_object*)&l_Lake_buildFileUnlessUpToDate_x27___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_saveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to cache artifact: "};
static const lean_object* l_Lake_Cache_saveArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_saveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_saveArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__1_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__2 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value),((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value),((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__3 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_cacheArtifact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_cacheArtifact___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_cacheArtifact___redArg___closed__0 = (const lean_object*)&l_Lake_cacheArtifact___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n- "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not write outputs to cache: "};
static const lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "downloaded succeeded, but artifact failed to resolve: "};
static const lean_object* l_Lake_resolveArtifact___lam__1___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "downloaded artifact "};
static const lean_object* l_Lake_resolveArtifact___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___closed__0_value;
static const lean_string_object l_Lake_resolveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_resolveArtifact___closed__1 = (const lean_object*)&l_Lake_resolveArtifact___closed__1_value;
static const lean_string_object l_Lake_resolveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_resolveArtifact___closed__2 = (const lean_object*)&l_Lake_resolveArtifact___closed__2_value;
static const lean_string_object l_Lake_resolveArtifact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "could not mark downloaded artifact read-only: "};
static const lean_object* l_Lake_resolveArtifact___closed__3 = (const lean_object*)&l_Lake_resolveArtifact___closed__3_value;
static const lean_string_object l_Lake_resolveArtifact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "artifact with associated cache service but no scope"};
static const lean_object* l_Lake_resolveArtifact___closed__4 = (const lean_object*)&l_Lake_resolveArtifact___closed__4_value;
static const lean_ctor_object l_Lake_resolveArtifact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_resolveArtifact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_resolveArtifact___closed__5 = (const lean_object*)&l_Lake_resolveArtifact___closed__5_value;
static const lean_string_object l_Lake_resolveArtifact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "artifact cache service is not configured: "};
static const lean_object* l_Lake_resolveArtifact___closed__6 = (const lean_object*)&l_Lake_resolveArtifact___closed__6_value;
static const lean_string_object l_Lake_resolveArtifact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "artifact not found in cache:\n  "};
static const lean_object* l_Lake_resolveArtifact___closed__7 = (const lean_object*)&l_Lake_resolveArtifact___closed__7_value;
static const lean_string_object l_Lake_resolveArtifact___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_resolveArtifact___closed__8 = (const lean_object*)&l_Lake_resolveArtifact___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifactOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output:\n"};
static const lean_object* l_Lake_resolveArtifactOutput___closed__0 = (const lean_object*)&l_Lake_resolveArtifactOutput___closed__0_value;
static const lean_string_object l_Lake_resolveArtifactOutput___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_resolveArtifactOutput___closed__1 = (const lean_object*)&l_Lake_resolveArtifactOutput___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_restoreArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "restored artifact from cache to: "};
static const lean_object* l_Lake_restoreArtifact___closed__0 = (const lean_object*)&l_Lake_restoreArtifact___closed__0_value;
static const lean_string_object l_Lake_restoreArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "found artifact in cache: "};
static const lean_object* l_Lake_restoreArtifact___closed__1 = (const lean_object*)&l_Lake_restoreArtifact___closed__1_value;
static const lean_string_object l_Lake_restoreArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "could not hard link artifact, copying from cache instead; error: "};
static const lean_object* l_Lake_restoreArtifact___closed__2 = (const lean_object*)&l_Lake_restoreArtifact___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "failed to retrieve artifact modification time: "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_inputBinFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_inputBinFile___redArg___closed__0 = (const lean_object*)&l_Lake_inputBinFile___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_inputDir___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_inputDir___lam__1___closed__0 = (const lean_object*)&l_Lake_inputDir___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_inputDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_inputDir___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_inputDir___closed__0 = (const lean_object*)&l_Lake_inputDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildO___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "traceArgs: "};
static const lean_object* l_Lake_buildO___lam__2___closed__0 = (const lean_object*)&l_Lake_buildO___lam__2___closed__0_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lake_buildO___lam__2___closed__1 = (const lean_object*)&l_Lake_buildO___lam__2___closed__1_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_buildO___lam__2___closed__2 = (const lean_object*)&l_Lake_buildO___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_buildO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_buildO___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__0 = (const lean_object*)&l_Lake_buildO___closed__0_value;
static const lean_closure_object l_Lake_buildO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__1 = (const lean_object*)&l_Lake_buildO___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildLeanO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lake_buildLeanO___lam__0___closed__0 = (const lean_object*)&l_Lake_buildLeanO___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_buildLeanO___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lake_buildStaticLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "objs"};
static const lean_object* l_Lake_buildStaticLib___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-l"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__0_value;
static const lean_array_object l_Lake_mkLinkOrder___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__1 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__1_value;
static const lean_ctor_object l_Lake_mkLinkOrder___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_mkLinkOrder___redArg___closed__1_value)}};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__2 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSharedLibSync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "MACOSX_DEPLOYMENT_TARGET: "};
static const lean_object* l_Lake_buildSharedLibSync___closed__0 = (const lean_object*)&l_Lake_buildSharedLibSync___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__14(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__12));
v___x_30_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
v___x_31_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_instMonadBaseIO;
v___x_33_ = l_Lake_instAlternativeELogTOfMonad___redArg(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__18(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__12));
v___x_38_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__14, &l_Lake_instMonadWorkspaceJobM___closed__14_once, _init_l_Lake_instMonadWorkspaceJobM___closed__14);
v___x_39_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19(void){
_start:
{
lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__18, &l_Lake_instMonadWorkspaceJobM___closed__18_once, _init_l_Lake_instMonadWorkspaceJobM___closed__18);
v___f_41_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__17));
v___x_42_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___x_42_, 0, v___f_41_);
lean_closure_set(v___x_42_, 1, lean_box(0));
lean_closure_set(v___x_42_, 2, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM(void){
_start:
{
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v_toBind_45_; lean_object* v_toFunctor_46_; lean_object* v_toPure_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_toApplicative_63_; lean_object* v_toFunctor_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_toApplicative_68_; lean_object* v_toFunctor_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_toApplicative_77_; lean_object* v_toFunctor_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_toApplicative_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_106_; 
v___x_43_ = l_instMonadBaseIO;
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_toBind_45_ = lean_ctor_get(v___x_43_, 1);
v_toFunctor_46_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toPure_47_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_inc_n(v_toBind_45_, 3);
lean_inc_n(v_toPure_47_, 5);
v___f_48_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_48_, 0, v_toPure_47_);
lean_closure_set(v___f_48_, 1, v_toBind_45_);
v___f_49_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_49_, 0, v_toPure_47_);
lean_closure_set(v___f_49_, 1, v_toBind_45_);
lean_inc_ref(v___f_48_);
v___f_50_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_50_, 0, v_toPure_47_);
lean_closure_set(v___f_50_, 1, v___f_48_);
lean_inc_ref_n(v_toFunctor_46_, 2);
v___f_51_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_51_, 0, v_toFunctor_46_);
lean_closure_set(v___f_51_, 1, v_toPure_47_);
lean_closure_set(v___f_51_, 2, v_toBind_45_);
v___x_52_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_46_);
v___f_53_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_53_, 0, v_toPure_47_);
lean_inc_ref_n(v___x_52_, 2);
v___x_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___f_53_);
lean_ctor_set(v___x_54_, 2, v___f_51_);
lean_ctor_set(v___x_54_, 3, v___f_50_);
lean_ctor_set(v___x_54_, 4, v___f_49_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___f_48_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_56_, 0, v___x_52_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_57_, 0, v___x_52_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___f_56_);
lean_ctor_set(v___x_58_, 1, v___f_57_);
v___x_59_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__15, &l_Lake_instMonadWorkspaceJobM___closed__15_once, _init_l_Lake_instMonadWorkspaceJobM___closed__15);
lean_inc_ref(v___x_55_);
v___x_60_ = l_ReaderT_instAlternativeOfMonad___redArg(v___x_59_, v___x_55_);
v___x_61_ = l_ReaderT_instMonad___redArg(v___x_55_);
lean_inc_ref(v___x_61_);
v___x_62_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v___x_60_, v___x_61_);
v_toApplicative_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_toApplicative_63_);
lean_dec_ref(v___x_62_);
v_toFunctor_64_ = lean_ctor_get(v_toApplicative_63_, 0);
lean_inc_ref_n(v_toFunctor_64_, 2);
lean_dec_ref(v_toApplicative_63_);
v___x_65_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__19, &l_Lake_instMonadWorkspaceJobM___closed__19_once, _init_l_Lake_instMonadWorkspaceJobM___closed__19);
lean_inc_ref(v___x_58_);
v___x_66_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_65_, v___x_58_);
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_61_);
v_toApplicative_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_toApplicative_68_);
v_toFunctor_69_ = lean_ctor_get(v_toApplicative_68_, 0);
lean_inc_ref_n(v_toFunctor_69_, 2);
lean_dec_ref(v_toApplicative_68_);
v___x_70_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_66_, v___x_58_);
v___x_71_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, lean_box(0));
lean_closure_set(v___x_71_, 2, lean_box(0));
lean_closure_set(v___x_71_, 3, lean_box(0));
lean_closure_set(v___x_71_, 4, v___x_70_);
v___x_72_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_71_, v_toFunctor_64_);
v___f_73_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_73_, 0, v_toFunctor_69_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toFunctor_69_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___f_73_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
v___x_76_ = l_ReaderT_instMonad___redArg(v___x_67_);
v_toApplicative_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toApplicative_77_);
v_toFunctor_78_ = lean_ctor_get(v_toApplicative_77_, 0);
lean_inc_ref_n(v_toFunctor_78_, 2);
lean_dec_ref(v_toApplicative_77_);
v___x_79_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_72_, v_toFunctor_64_);
v___x_80_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, v___x_79_);
lean_inc_ref(v___x_75_);
v___x_81_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_80_, v___x_75_);
v___x_82_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_81_, v___x_75_);
v___x_83_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_78_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toFunctor_78_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_84_);
lean_ctor_set(v___x_86_, 1, v___f_85_);
lean_inc_ref_n(v___x_86_, 2);
v___x_87_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_83_, v___x_86_);
v___x_88_ = l_Lake_EquipT_instFunctor___redArg(v___x_86_);
v_toApplicative_89_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_76_, 1);
lean_dec(v_unused_107_);
v___x_91_ = v___x_76_;
v_isShared_92_ = v_isSharedCheck_106_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_toApplicative_89_);
lean_dec(v___x_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_106_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_toFunctor_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_102_; 
v_toFunctor_93_ = lean_ctor_get(v_toApplicative_89_, 0);
lean_inc_ref_n(v_toFunctor_93_, 2);
lean_dec_ref(v_toApplicative_89_);
v___x_94_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_87_, v___x_86_);
v___x_95_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, lean_box(0));
lean_closure_set(v___x_95_, 2, lean_box(0));
lean_closure_set(v___x_95_, 3, v___x_94_);
lean_inc_ref(v___x_88_);
v___x_96_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_95_, v___x_88_);
v___x_97_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_96_, v___x_88_);
v___x_98_ = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_99_, 0, v_toFunctor_93_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_100_, 0, v_toFunctor_93_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___f_100_);
lean_ctor_set(v___x_91_, 0, v___f_99_);
v___x_102_ = v___x_91_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___f_99_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___f_100_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l_Lake_EquipT_instFunctor___redArg(v___x_102_);
v___x_104_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_98_, v___x_103_);
return v___x_104_;
}
}
}
}
static uint64_t _init_l_Lake_platformTrace___closed__0(void){
_start:
{
lean_object* v___x_108_; uint64_t v___x_109_; 
v___x_108_ = l_System_Platform_target;
v___x_109_ = lean_string_hash(v___x_108_);
return v___x_109_;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1(void){
_start:
{
uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; 
v___x_110_ = lean_uint64_once(&l_Lake_platformTrace___closed__0, &l_Lake_platformTrace___closed__0_once, _init_l_Lake_platformTrace___closed__0);
v___x_111_ = l_Lake_Hash_nil;
v___x_112_ = lean_uint64_mix_hash(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4(void){
_start:
{
uint32_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = 0;
v___x_118_ = lean_obj_once(&l_Lake_platformTrace___closed__3, &l_Lake_platformTrace___closed__3_once, _init_l_Lake_platformTrace___closed__3);
v___x_119_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set_uint32(v___x_119_, sizeof(void*)*1, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5(void){
_start:
{
lean_object* v___x_120_; uint64_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_121_ = lean_uint64_once(&l_Lake_platformTrace___closed__1, &l_Lake_platformTrace___closed__1_once, _init_l_Lake_platformTrace___closed__1);
v___x_122_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_123_ = l_System_Platform_target;
v___x_124_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_120_);
lean_ctor_set_uint64(v___x_124_, sizeof(void*)*3, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_platformTrace(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lake_platformTrace___closed__5, &l_Lake_platformTrace___closed__5_once, _init_l_Lake_platformTrace___closed__5);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* v_a_126_){
_start:
{
lean_object* v_log_128_; uint8_t v_action_129_; uint8_t v_wantsRebuild_130_; lean_object* v_trace_131_; lean_object* v_buildTime_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_log_128_ = lean_ctor_get(v_a_126_, 0);
v_action_129_ = lean_ctor_get_uint8(v_a_126_, sizeof(void*)*3);
v_wantsRebuild_130_ = lean_ctor_get_uint8(v_a_126_, sizeof(void*)*3 + 1);
v_trace_131_ = lean_ctor_get(v_a_126_, 1);
v_buildTime_132_ = lean_ctor_get(v_a_126_, 2);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_126_);
if (v_isSharedCheck_143_ == 0)
{
v___x_134_ = v_a_126_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_buildTime_132_);
lean_inc(v_trace_131_);
lean_inc(v_log_128_);
lean_dec(v_a_126_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_136_ = l_Lake_platformTrace;
v___x_137_ = lean_box(0);
v___x_138_ = l_Lake_BuildTrace_mix(v_trace_131_, v___x_136_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_138_);
v___x_140_ = v___x_134_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_log_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_buildTime_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3, v_action_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3 + 1, v_wantsRebuild_130_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_137_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lake_addPlatformTrace___redArg(v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_log_154_; uint8_t v_action_155_; uint8_t v_wantsRebuild_156_; lean_object* v_trace_157_; lean_object* v_buildTime_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_169_; 
v_log_154_ = lean_ctor_get(v_a_152_, 0);
v_action_155_ = lean_ctor_get_uint8(v_a_152_, sizeof(void*)*3);
v_wantsRebuild_156_ = lean_ctor_get_uint8(v_a_152_, sizeof(void*)*3 + 1);
v_trace_157_ = lean_ctor_get(v_a_152_, 1);
v_buildTime_158_ = lean_ctor_get(v_a_152_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v_a_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_160_ = v_a_152_;
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_buildTime_158_);
lean_inc(v_trace_157_);
lean_inc(v_log_154_);
lean_dec(v_a_152_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_162_ = l_Lake_platformTrace;
v___x_163_ = lean_box(0);
v___x_164_ = l_Lake_BuildTrace_mix(v_trace_157_, v___x_162_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_164_);
v___x_166_ = v___x_160_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_log_154_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_buildTime_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*3, v_action_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*3 + 1, v_wantsRebuild_156_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lake_addPlatformTrace(v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_log_181_; uint8_t v_action_182_; uint8_t v_wantsRebuild_183_; lean_object* v_trace_184_; lean_object* v_buildTime_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
v_log_181_ = lean_ctor_get(v_a_179_, 0);
v_action_182_ = lean_ctor_get_uint8(v_a_179_, sizeof(void*)*3);
v_wantsRebuild_183_ = lean_ctor_get_uint8(v_a_179_, sizeof(void*)*3 + 1);
v_trace_184_ = lean_ctor_get(v_a_179_, 1);
v_buildTime_185_ = lean_ctor_get(v_a_179_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_196_ == 0)
{
v___x_187_ = v_a_179_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_buildTime_185_);
lean_inc(v_trace_184_);
lean_inc(v_log_181_);
lean_dec(v_a_179_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_leanTrace_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v_leanTrace_189_ = lean_ctor_get(v_a_178_, 2);
v___x_190_ = lean_box(0);
lean_inc_ref(v_leanTrace_189_);
v___x_191_ = l_Lake_BuildTrace_mix(v_trace_184_, v_leanTrace_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_191_);
v___x_193_ = v___x_187_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_log_181_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_buildTime_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*3, v_action_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*3 + 1, v_wantsRebuild_183_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_addLeanTrace___redArg(v_a_197_, v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_log_208_; uint8_t v_action_209_; uint8_t v_wantsRebuild_210_; lean_object* v_trace_211_; lean_object* v_buildTime_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_223_; 
v_log_208_ = lean_ctor_get(v_a_206_, 0);
v_action_209_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*3);
v_wantsRebuild_210_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*3 + 1);
v_trace_211_ = lean_ctor_get(v_a_206_, 1);
v_buildTime_212_ = lean_ctor_get(v_a_206_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_223_ == 0)
{
v___x_214_ = v_a_206_;
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_buildTime_212_);
lean_inc(v_trace_211_);
lean_inc(v_log_208_);
lean_dec(v_a_206_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_leanTrace_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v_leanTrace_216_ = lean_ctor_get(v_a_205_, 2);
v___x_217_ = lean_box(0);
lean_inc_ref(v_leanTrace_216_);
v___x_218_ = l_Lake_BuildTrace_mix(v_trace_211_, v_leanTrace_216_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_218_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_log_208_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_buildTime_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*3, v_action_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*3 + 1, v_wantsRebuild_210_);
v___x_220_ = v_reuseFailAlloc_222_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_217_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_addLeanTrace(v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_a_235_, lean_object* v_caption_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_log_239_; uint8_t v_action_240_; uint8_t v_wantsRebuild_241_; lean_object* v_trace_242_; lean_object* v_buildTime_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_262_; 
v_log_239_ = lean_ctor_get(v_a_237_, 0);
v_action_240_ = lean_ctor_get_uint8(v_a_237_, sizeof(void*)*3);
v_wantsRebuild_241_ = lean_ctor_get_uint8(v_a_237_, sizeof(void*)*3 + 1);
v_trace_242_ = lean_ctor_get(v_a_237_, 1);
v_buildTime_243_ = lean_ctor_get(v_a_237_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_237_);
if (v_isSharedCheck_262_ == 0)
{
v___x_245_ = v_a_237_;
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_buildTime_243_);
lean_inc(v_trace_242_);
lean_inc(v_log_239_);
lean_dec(v_a_237_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint64_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
lean_inc(v_a_235_);
v___x_247_ = lean_apply_1(v_inst_234_, v_a_235_);
v___x_248_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_249_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_250_ = lean_string_append(v_caption_236_, v___x_249_);
v___x_251_ = lean_apply_1(v_inst_233_, v_a_235_);
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_254_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_248_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
v___x_255_ = lean_unbox_uint64(v___x_247_);
lean_dec_ref(v___x_247_);
lean_ctor_set_uint64(v___x_254_, sizeof(void*)*3, v___x_255_);
v___x_256_ = lean_box(0);
v___x_257_ = l_Lake_BuildTrace_mix(v_trace_242_, v___x_254_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_257_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_log_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_buildTime_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*3, v_action_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*3 + 1, v_wantsRebuild_241_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_a_265_, lean_object* v_caption_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_addPureTrace___redArg(v_inst_263_, v_inst_264_, v_a_265_, v_caption_266_, v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_a_273_, lean_object* v_caption_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_log_282_; uint8_t v_action_283_; uint8_t v_wantsRebuild_284_; lean_object* v_trace_285_; lean_object* v_buildTime_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_305_; 
v_log_282_ = lean_ctor_get(v_a_280_, 0);
v_action_283_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3);
v_wantsRebuild_284_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3 + 1);
v_trace_285_ = lean_ctor_get(v_a_280_, 1);
v_buildTime_286_ = lean_ctor_get(v_a_280_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_305_ == 0)
{
v___x_288_ = v_a_280_;
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_buildTime_286_);
lean_inc(v_trace_285_);
lean_inc(v_log_282_);
lean_dec(v_a_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint64_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_inc(v_a_273_);
v___x_290_ = lean_apply_1(v_inst_272_, v_a_273_);
v___x_291_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_292_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_293_ = lean_string_append(v_caption_274_, v___x_292_);
v___x_294_ = lean_apply_1(v_inst_271_, v_a_273_);
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_297_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_291_);
lean_ctor_set(v___x_297_, 2, v___x_296_);
v___x_298_ = lean_unbox_uint64(v___x_290_);
lean_dec_ref(v___x_290_);
lean_ctor_set_uint64(v___x_297_, sizeof(void*)*3, v___x_298_);
v___x_299_ = lean_box(0);
v___x_300_ = l_Lake_BuildTrace_mix(v_trace_285_, v___x_297_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_300_);
v___x_302_ = v___x_288_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_log_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_buildTime_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*3, v_action_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*3 + 1, v_wantsRebuild_284_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_299_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_a_309_, lean_object* v_caption_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lake_addPureTrace(v_00_u03b1_306_, v_inst_307_, v_inst_308_, v_a_309_, v_caption_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_val_323_; 
v_val_323_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_val_323_);
return v_val_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_326_, size_t v_i_327_, lean_object* v_bs_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_329_ == 0)
{
return v_bs_328_;
}
else
{
lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; lean_object* v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v_v_330_ = lean_array_uget(v_bs_328_, v_i_327_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_328_, v_i_327_, v___x_331_);
v___x_333_ = l_Lake_instToJsonLogEntry_toJson(v_v_330_);
lean_dec(v_v_330_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_327_, v___x_334_);
v___x_336_ = lean_array_uset(v_bs_x27_332_, v_i_327_, v___x_333_);
v_i_327_ = v___x_335_;
v_bs_328_ = v___x_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_bs_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_341_, v_i_boxed_342_, v_bs_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_344_){
_start:
{
size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_sz_345_ = lean_array_size(v_a_344_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_345_, v___x_346_, v_a_344_);
v___x_348_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_349_){
_start:
{
lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_fst_350_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_fst_350_);
v_snd_351_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_snd_351_);
lean_dec_ref(v_x_349_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v_fst_350_);
v___x_353_ = lean_unsigned_to_nat(2u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_array_push(v___x_354_, v___x_352_);
v___x_356_ = lean_array_push(v___x_355_, v_snd_351_);
v___x_357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_361_ == 0)
{
return v_bs_360_;
}
else
{
lean_object* v_v_362_; lean_object* v___x_363_; lean_object* v_bs_x27_364_; lean_object* v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v_v_362_ = lean_array_uget(v_bs_360_, v_i_359_);
v___x_363_ = lean_unsigned_to_nat(0u);
v_bs_x27_364_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_363_);
v___x_365_ = l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_362_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_359_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_364_, v_i_359_, v___x_365_);
v_i_359_ = v___x_367_;
v_bs_360_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_376_){
_start:
{
size_t v_sz_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_sz_377_ = lean_array_size(v_a_376_);
v___x_378_ = ((size_t)0ULL);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_377_, v___x_378_, v_a_376_);
v___x_380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__1));
v___x_385_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_386_ = lean_box(1);
v___x_387_ = l_Lake_JsonObject_insertJson(v___x_386_, v___x_385_, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* v_self_393_){
_start:
{
uint64_t v_depHash_394_; lean_object* v_inputs_395_; lean_object* v_outputs_x3f_396_; lean_object* v_log_397_; uint8_t v_synthetic_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_depHash_394_ = lean_ctor_get_uint64(v_self_393_, sizeof(void*)*3);
v_inputs_395_ = lean_ctor_get(v_self_393_, 0);
lean_inc_ref(v_inputs_395_);
v_outputs_x3f_396_ = lean_ctor_get(v_self_393_, 1);
lean_inc(v_outputs_x3f_396_);
v_log_397_ = lean_ctor_get(v_self_393_, 2);
lean_inc_ref(v_log_397_);
v_synthetic_398_ = lean_ctor_get_uint8(v_self_393_, sizeof(void*)*3 + 8);
lean_dec_ref(v_self_393_);
v___x_399_ = lean_obj_once(&l_Lake_BuildMetadata_toJson___closed__2, &l_Lake_BuildMetadata_toJson___closed__2_once, _init_l_Lake_BuildMetadata_toJson___closed__2);
v___x_400_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_401_ = l_Lake_lowerHexUInt64(v_depHash_394_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = l_Lake_JsonObject_insertJson(v___x_399_, v___x_400_, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_405_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_395_);
v___x_406_ = l_Lake_JsonObject_insertJson(v___x_403_, v___x_404_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_408_ = l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_396_);
lean_dec(v_outputs_x3f_396_);
v___x_409_ = l_Lake_JsonObject_insertJson(v___x_406_, v___x_407_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_411_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_397_);
v___x_412_ = l_Lake_JsonObject_insertJson(v___x_409_, v___x_410_, v___x_411_);
v___x_413_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_414_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_414_, 0, v_synthetic_398_);
v___x_415_ = l_Lake_JsonObject_insertJson(v___x_412_, v___x_413_, v___x_414_);
v___x_416_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t v_hash_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_422_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_423_ = lean_box(0);
v___x_424_ = 0;
v___x_425_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_422_);
lean_ctor_set_uint64(v___x_425_, sizeof(void*)*3, v_hash_421_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 8, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* v_hash_426_){
_start:
{
uint64_t v_hash_boxed_427_; lean_object* v_res_428_; 
v_hash_boxed_427_ = lean_unbox_uint64(v_hash_426_);
lean_dec_ref(v_hash_426_);
v_res_428_ = l_Lake_BuildMetadata_ofStub(v_hash_boxed_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Json_getBool_x3f(v_x_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_455_){
_start:
{
lean_object* v_j_457_; 
if (lean_obj_tag(v_x_455_) == 4)
{
lean_object* v_elems_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_elems_465_ = lean_ctor_get(v_x_455_, 0);
v___x_466_ = lean_array_get_size(v_elems_465_);
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = lean_nat_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
v_j_457_ = v_x_455_;
goto v___jp_456_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v_elems_465_);
lean_dec_ref_known(v_x_455_, 1);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_fget_borrowed(v_elems_465_, v___x_469_);
lean_inc(v___x_470_);
v___x_471_ = l_Lean_Json_getStr_x3f(v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_elems_465_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_array_fget(v_elems_465_, v___x_484_);
lean_dec_ref(v_elems_465_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_a_480_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_486_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
v_j_457_ = v_x_455_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_458_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_459_ = lean_unsigned_to_nat(80u);
v___x_460_ = l_Lean_Json_pretty(v_j_457_, v___x_459_);
v___x_461_ = lean_string_append(v___x_458_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_463_ = lean_string_append(v___x_461_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_bs_493_);
return v___x_495_;
}
else
{
lean_object* v_v_496_; lean_object* v___x_497_; 
v_v_496_ = lean_array_uget_borrowed(v_bs_493_, v_i_492_);
lean_inc(v_v_496_);
v___x_497_ = l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_bs_493_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v_bs_x27_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_a_506_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_497_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v_bs_x27_508_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_492_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_508_, v_i_492_, v_a_506_);
v_i_492_ = v___x_510_;
v_bs_493_ = v___x_511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 4)
{
lean_object* v_elems_521_; size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v_elems_521_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_elems_521_);
lean_dec_ref_known(v_x_520_, 1);
v_sz_522_ = lean_array_size(v_elems_521_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_522_, v___x_523_, v_elems_521_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_525_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0));
v___x_526_ = lean_unsigned_to_nat(80u);
v___x_527_ = l_Lean_Json_pretty(v_x_520_, v___x_526_);
v___x_528_ = lean_string_append(v___x_525_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v___x_535_; 
v___x_535_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
v_a_545_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_554_, size_t v_i_555_, lean_object* v_bs_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_bs_556_);
return v___x_558_;
}
else
{
lean_object* v_v_559_; lean_object* v___x_560_; 
v_v_559_ = lean_array_uget_borrowed(v_bs_556_, v_i_555_);
lean_inc(v_v_559_);
v___x_560_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v_bs_556_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v_bs_x27_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v_a_569_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_560_, 1);
v___x_570_ = lean_unsigned_to_nat(0u);
v_bs_x27_571_ = lean_array_uset(v_bs_556_, v_i_555_, v___x_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_555_, v___x_572_);
v___x_574_ = lean_array_uset(v_bs_x27_571_, v_i_555_, v_a_569_);
v_i_555_ = v___x_573_;
v_bs_556_ = v___x_574_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_bs_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_579_, v_i_boxed_580_, v_bs_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 4)
{
lean_object* v_elems_583_; size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; 
v_elems_583_ = lean_ctor_get(v_x_582_, 0);
lean_inc_ref(v_elems_583_);
lean_dec_ref_known(v_x_582_, 1);
v_sz_584_ = lean_array_size(v_elems_583_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_584_, v___x_585_, v_elems_583_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_587_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0));
v___x_588_ = lean_unsigned_to_nat(80u);
v___x_589_ = l_Lean_Json_pretty(v_x_582_, v___x_588_);
v___x_590_ = lean_string_append(v___x_587_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_596_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_a_607_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_598_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_598_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_a_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_x_618_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v___x_626_ = l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_624_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_a_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_651_){
_start:
{
lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint64_t v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint64_t v___y_664_; lean_object* v___y_667_; lean_object* v___y_668_; uint64_t v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; lean_object* v___y_698_; uint64_t v___y_699_; lean_object* v___y_702_; uint64_t v___y_703_; lean_object* v_a_704_; lean_object* v___y_730_; uint64_t v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_790_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_792_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_795_; 
v_val_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_792_, 1);
v___x_795_ = l_Lean_Json_getStr_x3f(v_val_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_805_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_805_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_801_ = lean_string_append(v___x_800_, v_a_796_);
lean_dec(v_a_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
else
{
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_795_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_795_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_795_, 1);
v___x_815_ = l_Lake_Hash_ofDecimal_x3f(v_a_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return v___x_816_;
}
else
{
lean_object* v_val_817_; uint64_t v___x_818_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_815_, 1);
v___x_818_ = lean_unbox_uint64(v_val_817_);
lean_dec(v_val_817_);
v_depHash_764_ = v___x_818_;
goto v___jp_763_;
}
}
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_819_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_820_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_821_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_823_; 
v_val_822_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_820_, 1);
v___x_823_ = l_Lake_Hash_fromJson_x3f(v_val_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_833_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_828_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_829_ = lean_string_append(v___x_828_, v_a_824_);
lean_dec(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_823_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; uint64_t v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_823_, 1);
v___x_843_ = lean_unbox_uint64(v_a_842_);
lean_dec(v_a_842_);
v_depHash_764_ = v___x_843_;
goto v___jp_763_;
}
}
}
}
v___jp_652_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_658_, 0, v___y_654_);
lean_ctor_set(v___x_658_, 1, v___y_653_);
lean_ctor_set(v___x_658_, 2, v___y_655_);
lean_ctor_set_uint64(v___x_658_, sizeof(void*)*3, v___y_656_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*3 + 8, v_a_657_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
v___jp_660_:
{
uint8_t v___x_665_; 
v___x_665_ = 0;
v___y_653_ = v___y_661_;
v___y_654_ = v___y_662_;
v___y_655_ = v___y_663_;
v___y_656_ = v___y_664_;
v_a_657_ = v___x_665_;
goto v___jp_652_;
}
v___jp_666_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_672_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
v___y_661_ = v___y_667_;
v___y_662_ = v___y_668_;
v___y_663_ = v_a_670_;
v___y_664_ = v___y_669_;
goto v___jp_660_;
}
else
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_673_);
lean_dec(v_val_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_a_670_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_684_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
v___x_680_ = lean_string_append(v___x_679_, v_a_675_);
lean_dec(v_a_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_a_670_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
v_a_685_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_674_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_674_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 0);
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_674_, 1);
if (lean_obj_tag(v_a_693_) == 0)
{
v___y_661_ = v___y_667_;
v___y_662_ = v___y_668_;
v___y_663_ = v_a_670_;
v___y_664_ = v___y_669_;
goto v___jp_660_;
}
else
{
lean_object* v_val_694_; uint8_t v___x_695_; 
v_val_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_a_693_, 1);
v___x_695_ = lean_unbox(v_val_694_);
lean_dec(v_val_694_);
v___y_653_ = v___y_667_;
v___y_654_ = v___y_668_;
v___y_655_ = v_a_670_;
v___y_656_ = v___y_669_;
v_a_657_ = v___x_695_;
goto v___jp_652_;
}
}
}
}
}
v___jp_696_:
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___y_667_ = v___y_697_;
v___y_668_ = v___y_698_;
v___y_669_ = v___y_699_;
v_a_670_ = v___x_700_;
goto v___jp_666_;
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_706_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
v___y_697_ = v_a_704_;
v___y_698_ = v___y_702_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_704_);
lean_dec_ref(v___y_702_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
v___x_714_ = lean_string_append(v___x_713_, v_a_709_);
lean_dec(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_704_);
lean_dec_ref(v___y_702_);
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_708_, 1);
if (lean_obj_tag(v_a_727_) == 0)
{
v___y_697_ = v_a_704_;
v___y_698_ = v___y_702_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_a_727_, 1);
v___y_667_ = v_a_704_;
v___y_668_ = v___y_702_;
v___y_669_ = v___y_703_;
v_a_670_ = v_val_728_;
goto v___jp_666_;
}
}
}
}
}
v___jp_729_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
v___y_702_ = v___y_730_;
v___y_703_ = v___y_731_;
v_a_704_ = v___x_732_;
goto v___jp_701_;
}
v___jp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_737_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
v___y_730_ = v_a_735_;
v___y_731_ = v___y_734_;
goto v___jp_729_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_a_735_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
v___x_745_ = lean_string_append(v___x_744_, v_a_740_);
lean_dec(v_a_740_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_a_735_);
v_a_750_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_739_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_739_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; 
v_a_758_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_739_, 1);
if (lean_obj_tag(v_a_758_) == 0)
{
v___y_730_ = v_a_735_;
v___y_731_ = v___y_734_;
goto v___jp_729_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_a_758_, 1);
v___y_702_ = v_a_735_;
v___y_703_ = v___y_734_;
v_a_704_ = v_val_759_;
goto v___jp_701_;
}
}
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___y_734_ = v___y_761_;
v_a_735_ = v___x_762_;
goto v___jp_733_;
}
v___jp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_766_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
v___y_761_ = v_depHash_764_;
goto v___jp_760_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_778_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_778_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
v___x_774_ = lean_string_append(v___x_773_, v_a_769_);
lean_dec(v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_768_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_768_, 1);
if (lean_obj_tag(v_a_787_) == 0)
{
v___y_761_ = v_depHash_764_;
goto v___jp_760_;
}
else
{
lean_object* v_val_788_; 
v_val_788_ = lean_ctor_get(v_a_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_a_787_, 1);
v___y_734_ = v_depHash_764_;
v_a_735_ = v_val_788_;
goto v___jp_733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* v_obj_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_obj_844_);
lean_dec(v_obj_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* v_json_852_){
_start:
{
switch(lean_obj_tag(v_json_852_))
{
case 2:
{
lean_object* v_n_853_; lean_object* v___x_854_; 
v_n_853_ = lean_ctor_get(v_json_852_, 0);
v___x_854_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_859_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
v___x_860_ = lean_string_append(v___x_859_, v_a_855_);
lean_dec(v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_874_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint64_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_unbox_uint64(v_a_865_);
lean_dec(v_a_865_);
v___x_870_ = l_Lake_BuildMetadata_ofStub(v___x_869_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
case 5:
{
lean_object* v_kvPairs_875_; lean_object* v___x_876_; 
v_kvPairs_875_ = lean_ctor_get(v_json_852_, 0);
v___x_876_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_kvPairs_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_902_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_902_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_888_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_875_, v___x_887_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_888_, 1);
if (lean_obj_tag(v_val_889_) == 3)
{
lean_object* v_s_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_901_; 
v_s_890_ = lean_ctor_get(v_val_889_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_val_889_);
if (v_isSharedCheck_901_ == 0)
{
v___x_892_ = v_val_889_;
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_s_890_);
lean_dec(v_val_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
v___x_895_ = lean_string_dec_eq(v_s_890_, v___x_894_);
lean_dec_ref(v_s_890_);
if (v___x_895_ == 0)
{
lean_del_object(v___x_892_);
goto v___jp_881_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_del_object(v___x_879_);
v___x_896_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
v___x_897_ = lean_string_append(v___x_896_, v_a_877_);
lean_dec(v_a_877_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_dec(v_val_889_);
goto v___jp_881_;
}
}
else
{
lean_dec(v___x_888_);
goto v___jp_881_;
}
v___jp_881_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_882_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
v___x_883_ = lean_string_append(v___x_882_, v_a_877_);
lean_dec(v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
return v___x_876_;
}
}
default: 
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* v_json_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lake_BuildMetadata_fromJson_x3f(v_json_904_);
lean_dec(v_json_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* v_contents_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Json_parse(v_contents_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_909_, 1);
v___x_919_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_918_);
lean_dec(v_a_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t v_inputHash_920_, lean_object* v_outputs_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_outputs_921_);
v___x_924_ = 1;
v___x_925_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_925_, 0, v___x_922_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_922_);
lean_ctor_set_uint64(v___x_925_, sizeof(void*)*3, v_inputHash_920_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*3 + 8, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* v_inputHash_926_, lean_object* v_outputs_927_){
_start:
{
uint64_t v_inputHash_boxed_928_; lean_object* v_res_929_; 
v_inputHash_boxed_928_ = lean_unbox_uint64(v_inputHash_926_);
lean_dec_ref(v_inputHash_926_);
v_res_929_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_boxed_928_, v_outputs_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_, lean_object* v_b_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___y_937_; lean_object* v_inputs_944_; uint64_t v_hash_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_935_ = lean_array_uget_borrowed(v_as_930_, v_i_931_);
v_inputs_944_ = lean_ctor_get(v___x_935_, 1);
v_hash_945_ = lean_ctor_get_uint64(v___x_935_, sizeof(void*)*3);
v___x_946_ = lean_array_get_size(v_inputs_944_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_nat_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_944_);
v___x_950_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_949_);
v___y_937_ = v___x_950_;
goto v___jp_936_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Lake_lowerHexUInt64(v_hash_945_);
v___x_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
v___y_937_ = v___x_952_;
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v_caption_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v___x_941_; size_t v___x_942_; 
v_caption_938_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_caption_938_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_caption_938_);
lean_ctor_set(v___x_939_, 1, v___y_937_);
v___x_940_ = lean_array_push(v_b_933_, v___x_939_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_931_, v___x_941_);
v_i_931_ = v___x_942_;
v_b_933_ = v___x_940_;
goto _start;
}
}
else
{
return v_b_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* v_inputs_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___x_956_ = lean_array_get_size(v_inputs_953_);
v___x_957_ = lean_nat_dec_lt(v___x_954_, v___x_956_);
if (v___x_957_ == 0)
{
return v___x_955_;
}
else
{
uint8_t v___x_958_; 
v___x_958_ = lean_nat_dec_le(v___x_956_, v___x_956_);
if (v___x_958_ == 0)
{
if (v___x_957_ == 0)
{
return v___x_955_;
}
else
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((size_t)0ULL);
v___x_960_ = lean_usize_of_nat(v___x_956_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_953_, v___x_959_, v___x_960_, v___x_955_);
return v___x_961_;
}
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_956_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_953_, v___x_962_, v___x_963_, v___x_955_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* v_inputs_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_965_);
lean_dec_ref(v_inputs_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* v_as_967_, lean_object* v_i_968_, lean_object* v_stop_969_, lean_object* v_b_970_){
_start:
{
size_t v_i_boxed_971_; size_t v_stop_boxed_972_; lean_object* v_res_973_; 
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_stop_boxed_972_ = lean_unbox_usize(v_stop_969_);
lean_dec(v_stop_969_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_as_967_, v_i_boxed_971_, v_stop_boxed_972_, v_b_970_);
lean_dec_ref(v_as_967_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* v_depTrace_974_, lean_object* v_outputs_975_, lean_object* v_log_976_){
_start:
{
lean_object* v_inputs_977_; uint64_t v_hash_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_inputs_977_ = lean_ctor_get(v_depTrace_974_, 1);
v_hash_978_ = lean_ctor_get_uint64(v_depTrace_974_, sizeof(void*)*3);
v___x_979_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_977_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_outputs_975_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_982_, 0, v___x_979_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
lean_ctor_set(v___x_982_, 2, v_log_976_);
lean_ctor_set_uint64(v___x_982_, sizeof(void*)*3, v_hash_978_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*3 + 8, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* v_depTrace_983_, lean_object* v_outputs_984_, lean_object* v_log_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_983_, v_outputs_984_, v_log_985_);
lean_dec_ref(v_depTrace_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* v_inst_987_, lean_object* v_depTrace_988_, lean_object* v_outputs_989_, lean_object* v_log_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_apply_1(v_inst_987_, v_outputs_989_);
v___x_992_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_988_, v___x_991_, v_log_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* v_inst_993_, lean_object* v_depTrace_994_, lean_object* v_outputs_995_, lean_object* v_log_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lake_BuildMetadata_ofBuild___redArg(v_inst_993_, v_depTrace_994_, v_outputs_995_, v_log_996_);
lean_dec_ref(v_depTrace_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* v_00_u03b1_998_, lean_object* v_inst_999_, lean_object* v_depTrace_1000_, lean_object* v_outputs_1001_, lean_object* v_log_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_apply_1(v_inst_999_, v_outputs_1001_);
v___x_1004_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1000_, v___x_1003_, v_log_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_depTrace_1007_, lean_object* v_outputs_1008_, lean_object* v_log_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lake_BuildMetadata_ofBuild(v_00_u03b1_1005_, v_inst_1006_, v_depTrace_1007_, v_outputs_1008_, v_log_1009_);
lean_dec_ref(v_depTrace_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* v_x_1011_){
_start:
{
switch(lean_obj_tag(v_x_1011_))
{
case 0:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
return v___x_1012_;
}
case 1:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(1u);
return v___x_1013_;
}
default: 
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_unsigned_to_nat(2u);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lake_SavedTrace_ctorIdx(v_x_1015_);
lean_dec(v_x_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* v_t_1017_, lean_object* v_k_1018_){
_start:
{
if (lean_obj_tag(v_t_1017_) == 2)
{
lean_object* v_data_1019_; lean_object* v___x_1020_; 
v_data_1019_ = lean_ctor_get(v_t_1017_, 0);
lean_inc_ref(v_data_1019_);
lean_dec_ref_known(v_t_1017_, 1);
v___x_1020_ = lean_apply_1(v_k_1018_, v_data_1019_);
return v___x_1020_;
}
else
{
lean_dec(v_t_1017_);
return v_k_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* v_motive_1021_, lean_object* v_ctorIdx_1022_, lean_object* v_t_1023_, lean_object* v_h_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1023_, v_k_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* v_motive_1027_, lean_object* v_ctorIdx_1028_, lean_object* v_t_1029_, lean_object* v_h_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lake_SavedTrace_ctorElim(v_motive_1027_, v_ctorIdx_1028_, v_t_1029_, v_h_1030_, v_k_1031_);
lean_dec(v_ctorIdx_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* v_t_1033_, lean_object* v_missing_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1033_, v_missing_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* v_motive_1036_, lean_object* v_t_1037_, lean_object* v_h_1038_, lean_object* v_missing_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1037_, v_missing_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* v_t_1041_, lean_object* v_invalid_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1041_, v_invalid_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* v_motive_1044_, lean_object* v_t_1045_, lean_object* v_h_1046_, lean_object* v_invalid_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1045_, v_invalid_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* v_t_1049_, lean_object* v_ok_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1049_, v_ok_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* v_motive_1052_, lean_object* v_t_1053_, lean_object* v_h_1054_, lean_object* v_ok_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1053_, v_ok_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* v_path_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_IO_FS_readFile(v_path_1058_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v_a_1064_; lean_object* v___x_1073_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1073_ = l_Lean_Json_parse(v_a_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_a_1064_ = v_a_1074_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1076_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_1075_);
lean_dec(v_a_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v_a_1064_ = v_a_1077_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_path_1058_);
v_a_1078_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v___x_1076_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 2);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1059_);
return v___x_1084_;
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1065_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_1066_ = lean_string_append(v_path_1058_, v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1066_, v_a_1064_);
lean_dec_ref(v_a_1064_);
v___x_1068_ = 2;
v___x_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_array_push(v_a_1059_, v___x_1069_);
v___x_1071_ = lean_box(1);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1070_);
return v___x_1072_;
}
}
else
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1061_, 1);
if (lean_obj_tag(v_a_1087_) == 11)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref_known(v_a_1087_, 2);
lean_dec_ref(v_path_1058_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1059_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1090_ = ((lean_object*)(l_Lake_readTraceFile___closed__0));
v___x_1091_ = lean_string_append(v_path_1058_, v___x_1090_);
v___x_1092_ = lean_io_error_to_string(v_a_1087_);
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = 3;
v___x_1095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1094_);
v___x_1096_ = lean_array_get_size(v_a_1059_);
v___x_1097_ = lean_array_push(v_a_1059_, v___x_1095_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* v_path_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lake_readTraceFile(v_path_1099_, v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* v_path_1103_, lean_object* v_data_1104_){
_start:
{
lean_object* v___x_1106_; 
lean_inc_ref(v_path_1103_);
v___x_1106_ = l_Lake_createParentDirs(v_path_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec_ref_known(v___x_1106_, 1);
v___x_1107_ = l_Lake_BuildMetadata_toJson(v_data_1104_);
v___x_1108_ = lean_unsigned_to_nat(80u);
v___x_1109_ = l_Lean_Json_pretty(v___x_1107_, v___x_1108_);
v___x_1110_ = l_IO_FS_writeFile(v_path_1103_, v___x_1109_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_path_1103_);
return v___x_1110_;
}
else
{
lean_dec_ref(v_data_1104_);
lean_dec_ref(v_path_1103_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* v_path_1111_, lean_object* v_data_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lake_BuildMetadata_writeFile(v_path_1111_, v_data_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* v_path_1115_, uint64_t v_inputHash_1116_, lean_object* v_outputs_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_1116_, v_outputs_1117_);
v___x_1120_ = l_Lake_BuildMetadata_writeFile(v_path_1115_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* v_path_1121_, lean_object* v_inputHash_1122_, lean_object* v_outputs_1123_, lean_object* v_a_1124_){
_start:
{
uint64_t v_inputHash_boxed_1125_; lean_object* v_res_1126_; 
v_inputHash_boxed_1125_ = lean_unbox_uint64(v_inputHash_1122_);
lean_dec_ref(v_inputHash_1122_);
v_res_1126_ = l_Lake_writeFetchTrace(v_path_1121_, v_inputHash_boxed_1125_, v_outputs_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* v_inst_1127_, lean_object* v_path_1128_, lean_object* v_depTrace_1129_, lean_object* v_outputs_1130_, lean_object* v_log_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_apply_1(v_inst_1127_, v_outputs_1130_);
v___x_1134_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1129_, v___x_1133_, v_log_1131_);
v___x_1135_ = l_Lake_BuildMetadata_writeFile(v_path_1128_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* v_inst_1136_, lean_object* v_path_1137_, lean_object* v_depTrace_1138_, lean_object* v_outputs_1139_, lean_object* v_log_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lake_writeBuildTrace___redArg(v_inst_1136_, v_path_1137_, v_depTrace_1138_, v_outputs_1139_, v_log_1140_);
lean_dec_ref(v_depTrace_1138_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* v_00_u03b1_1143_, lean_object* v_inst_1144_, lean_object* v_path_1145_, lean_object* v_depTrace_1146_, lean_object* v_outputs_1147_, lean_object* v_log_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_apply_1(v_inst_1144_, v_outputs_1147_);
v___x_1151_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1146_, v___x_1150_, v_log_1148_);
v___x_1152_ = l_Lake_BuildMetadata_writeFile(v_path_1145_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_inst_1154_, lean_object* v_path_1155_, lean_object* v_depTrace_1156_, lean_object* v_outputs_1157_, lean_object* v_log_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lake_writeBuildTrace(v_00_u03b1_1153_, v_inst_1154_, v_path_1155_, v_depTrace_1156_, v_outputs_1157_, v_log_1158_);
lean_dec_ref(v_depTrace_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t v_x_1161_){
_start:
{
switch(v_x_1161_)
{
case 0:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
return v___x_1162_;
}
case 1:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(2u);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* v_x_1165_){
_start:
{
uint8_t v_x_boxed_1166_; lean_object* v_res_1167_; 
v_x_boxed_1166_ = lean_unbox(v_x_1165_);
v_res_1167_ = l_Lake_OutputStatus_ctorIdx(v_x_boxed_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1168_){
_start:
{
lean_inc(v_k_1168_);
return v_k_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1169_);
lean_dec(v_k_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1171_, lean_object* v_ctorIdx_1172_, uint8_t v_t_1173_, lean_object* v_h_1174_, lean_object* v_k_1175_){
_start:
{
lean_inc(v_k_1175_);
return v_k_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1176_, lean_object* v_ctorIdx_1177_, lean_object* v_t_1178_, lean_object* v_h_1179_, lean_object* v_k_1180_){
_start:
{
uint8_t v_t_boxed_1181_; lean_object* v_res_1182_; 
v_t_boxed_1181_ = lean_unbox(v_t_1178_);
v_res_1182_ = l_Lake_OutputStatus_ctorElim(v_motive_1176_, v_ctorIdx_1177_, v_t_boxed_1181_, v_h_1179_, v_k_1180_);
lean_dec(v_k_1180_);
lean_dec(v_ctorIdx_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1183_){
_start:
{
lean_inc(v_outOfDate_1183_);
return v_outOfDate_1183_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1184_);
lean_dec(v_outOfDate_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1186_, uint8_t v_t_1187_, lean_object* v_h_1188_, lean_object* v_outOfDate_1189_){
_start:
{
lean_inc(v_outOfDate_1189_);
return v_outOfDate_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1190_, lean_object* v_t_1191_, lean_object* v_h_1192_, lean_object* v_outOfDate_1193_){
_start:
{
uint8_t v_t_boxed_1194_; lean_object* v_res_1195_; 
v_t_boxed_1194_ = lean_unbox(v_t_1191_);
v_res_1195_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1190_, v_t_boxed_1194_, v_h_1192_, v_outOfDate_1193_);
lean_dec(v_outOfDate_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1196_){
_start:
{
lean_inc(v_mtimeUpToDate_1196_);
return v_mtimeUpToDate_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1197_);
lean_dec(v_mtimeUpToDate_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1199_, uint8_t v_t_1200_, lean_object* v_h_1201_, lean_object* v_mtimeUpToDate_1202_){
_start:
{
lean_inc(v_mtimeUpToDate_1202_);
return v_mtimeUpToDate_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1203_, lean_object* v_t_1204_, lean_object* v_h_1205_, lean_object* v_mtimeUpToDate_1206_){
_start:
{
uint8_t v_t_boxed_1207_; lean_object* v_res_1208_; 
v_t_boxed_1207_ = lean_unbox(v_t_1204_);
v_res_1208_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1203_, v_t_boxed_1207_, v_h_1205_, v_mtimeUpToDate_1206_);
lean_dec(v_mtimeUpToDate_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1209_){
_start:
{
lean_inc(v_hashUpToDate_1209_);
return v_hashUpToDate_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1210_);
lean_dec(v_hashUpToDate_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1212_, uint8_t v_t_1213_, lean_object* v_h_1214_, lean_object* v_hashUpToDate_1215_){
_start:
{
lean_inc(v_hashUpToDate_1215_);
return v_hashUpToDate_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1216_, lean_object* v_t_1217_, lean_object* v_h_1218_, lean_object* v_hashUpToDate_1219_){
_start:
{
uint8_t v_t_boxed_1220_; lean_object* v_res_1221_; 
v_t_boxed_1220_ = lean_unbox(v_t_1217_);
v_res_1221_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1216_, v_t_boxed_1220_, v_h_1218_, v_hashUpToDate_1219_);
lean_dec(v_hashUpToDate_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_nat_dec_le(v_n_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_dec_le(v_n_1222_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = 2;
return v___x_1227_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
return v___x_1228_;
}
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Lake_OutputStatus_ofNat(v_n_1230_);
lean_dec(v_n_1230_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1233_, uint8_t v_y_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = l_Lake_OutputStatus_ctorIdx(v_x_1233_);
v___x_1236_ = l_Lake_OutputStatus_ctorIdx(v_y_1234_);
v___x_1237_ = lean_nat_dec_eq(v___x_1235_, v___x_1236_);
lean_dec(v___x_1236_);
lean_dec(v___x_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1238_, lean_object* v_y_1239_){
_start:
{
uint8_t v_x_13__boxed_1240_; uint8_t v_y_14__boxed_1241_; uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_x_13__boxed_1240_ = lean_unbox(v_x_1238_);
v_y_14__boxed_1241_ = lean_unbox(v_y_1239_);
v_res_1242_ = l_Lake_instDecidableEqOutputStatus(v_x_13__boxed_1240_, v_y_14__boxed_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1244_){
_start:
{
if (v_upToDate_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 2;
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1247_){
_start:
{
uint8_t v_upToDate_boxed_1248_; uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_upToDate_boxed_1248_ = lean_unbox(v_upToDate_1247_);
v_res_1249_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1248_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1251_){
_start:
{
if (v_upToDate_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 1;
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1254_){
_start:
{
uint8_t v_upToDate_boxed_1255_; uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_upToDate_boxed_1255_ = lean_unbox(v_upToDate_1254_);
v_res_1256_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1258_){
_start:
{
uint8_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = 0;
v___x_1260_ = l_Lake_instDecidableEqOutputStatus(v_status_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = 1;
return v___x_1261_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1263_){
_start:
{
uint8_t v_status_boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_status_boxed_1264_ = lean_unbox(v_status_1263_);
v_res_1265_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1267_){
_start:
{
uint8_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 1;
v___x_1269_ = l_Lake_instDecidableEqOutputStatus(v_status_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = 1;
return v___x_1270_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = 0;
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1272_){
_start:
{
uint8_t v_status_boxed_1273_; uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_status_boxed_1273_ = lean_unbox(v_status_1272_);
v_res_1274_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___f_1277_; 
v___x_1276_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1277_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1277_, 0, v___x_1276_);
return v___f_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_info_1280_, lean_object* v_depTrace_1281_, lean_object* v_depHash_1282_, lean_object* v_oldTrace_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
uint64_t v_hash_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_hash_1287_ = lean_ctor_get_uint64(v_depTrace_1281_, sizeof(void*)*3);
v___f_1288_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1289_ = lean_box_uint64(v_hash_1287_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___x_1291_ = l_Option_instBEq_beq___redArg(v___f_1288_, v___x_1290_, v_depHash_1282_);
if (v___x_1291_ == 0)
{
lean_object* v_toBuildConfig_1292_; uint8_t v_oldMode_1293_; 
lean_dec_ref(v_inst_1278_);
v_toBuildConfig_1292_ = lean_ctor_get(v_a_1284_, 0);
v_oldMode_1293_ = lean_ctor_get_uint8(v_toBuildConfig_1292_, sizeof(void*)*4);
if (v_oldMode_1293_ == 0)
{
uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v_info_1280_);
lean_dec_ref(v_inst_1279_);
v___x_1294_ = 0;
v___x_1295_ = lean_box(v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v_a_1285_);
return v___x_1296_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1279_, v_info_1280_, v_oldTrace_1283_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = 0;
v___x_1299_ = lean_box(v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_a_1285_);
return v___x_1300_;
}
else
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = 1;
v___x_1302_ = lean_box(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v_a_1285_);
return v___x_1303_;
}
}
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_dec_ref(v_inst_1279_);
v___x_1304_ = lean_apply_2(v_inst_1278_, v_info_1280_, lean_box(0));
v___x_1305_ = lean_unbox(v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = 0;
v___x_1307_ = lean_box(v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_a_1285_);
return v___x_1308_;
}
else
{
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = 2;
v___x_1310_ = lean_box(v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_1285_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_info_1314_, lean_object* v_depTrace_1315_, lean_object* v_depHash_1316_, lean_object* v_oldTrace_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1312_, v_inst_1313_, v_info_1314_, v_depTrace_1315_, v_depHash_1316_, v_oldTrace_1317_, v_a_1318_, v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec_ref(v_oldTrace_1317_);
lean_dec_ref(v_depTrace_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_info_1325_, lean_object* v_depTrace_1326_, lean_object* v_depHash_1327_, lean_object* v_oldTrace_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1323_, v_inst_1324_, v_info_1325_, v_depTrace_1326_, v_depHash_1327_, v_oldTrace_1328_, v_a_1333_, v_a_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_info_1340_, lean_object* v_depTrace_1341_, lean_object* v_depHash_1342_, lean_object* v_oldTrace_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1337_, v_inst_1338_, v_inst_1339_, v_info_1340_, v_depTrace_1341_, v_depHash_1342_, v_oldTrace_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec_ref(v_oldTrace_1343_);
lean_dec_ref(v_depTrace_1341_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_info_1354_, lean_object* v_depTrace_1355_, lean_object* v_depHash_1356_, lean_object* v_oldTrace_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1380_; 
v___x_1361_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1352_, v_inst_1353_, v_info_1354_, v_depTrace_1355_, v_depHash_1356_, v_oldTrace_1357_, v_a_1358_, v_a_1359_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_a_1363_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1380_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1380_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___x_1367_; uint8_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = 0;
v___x_1368_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
v___x_1369_ = l_Lake_instDecidableEqOutputStatus(v___x_1368_, v___x_1367_);
if (v___x_1369_ == 0)
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = 1;
v___x_1371_ = lean_box(v___x_1370_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1371_);
v___x_1373_ = v___x_1365_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_a_1363_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = 0;
v___x_1376_ = lean_box(v___x_1375_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1376_);
v___x_1378_ = v___x_1365_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1363_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_info_1383_, lean_object* v_depTrace_1384_, lean_object* v_depHash_1385_, lean_object* v_oldTrace_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lake_checkHashUpToDate___redArg(v_inst_1381_, v_inst_1382_, v_info_1383_, v_depTrace_1384_, v_depHash_1385_, v_oldTrace_1386_, v_a_1387_, v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec_ref(v_oldTrace_1386_);
lean_dec_ref(v_depTrace_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_info_1394_, lean_object* v_depTrace_1395_, lean_object* v_depHash_1396_, lean_object* v_oldTrace_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1424_; 
v___x_1405_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1392_, v_inst_1393_, v_info_1394_, v_depTrace_1395_, v_depHash_1396_, v_oldTrace_1397_, v_a_1402_, v_a_1403_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1409_ = v___x_1405_;
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v___x_1411_; uint8_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = 0;
v___x_1412_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
v___x_1413_ = l_Lake_instDecidableEqOutputStatus(v___x_1412_, v___x_1411_);
if (v___x_1413_ == 0)
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = 1;
v___x_1415_ = lean_box(v___x_1414_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1415_);
v___x_1417_ = v___x_1409_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1407_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = 0;
v___x_1420_ = lean_box(v___x_1419_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1420_);
v___x_1422_ = v___x_1409_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1407_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_info_1428_, lean_object* v_depTrace_1429_, lean_object* v_depHash_1430_, lean_object* v_oldTrace_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lake_checkHashUpToDate(v_00_u03b9_1425_, v_inst_1426_, v_inst_1427_, v_info_1428_, v_depTrace_1429_, v_depHash_1430_, v_oldTrace_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec_ref(v_oldTrace_1431_);
lean_dec_ref(v_depTrace_1429_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1440_, size_t v_i_1441_, size_t v_stop_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_eq(v_i_1441_, v_stop_1442_);
if (v___x_1446_ == 0)
{
lean_object* v_log_1447_; uint8_t v_action_1448_; uint8_t v_wantsRebuild_1449_; lean_object* v_trace_1450_; lean_object* v_buildTime_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1464_; 
v_log_1447_ = lean_ctor_get(v___y_1444_, 0);
v_action_1448_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*3);
v_wantsRebuild_1449_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*3 + 1);
v_trace_1450_ = lean_ctor_get(v___y_1444_, 1);
v_buildTime_1451_ = lean_ctor_get(v___y_1444_, 2);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___y_1444_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1453_ = v___y_1444_;
v_isShared_1454_ = v_isSharedCheck_1464_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_buildTime_1451_);
lean_inc(v_trace_1450_);
lean_inc(v_log_1447_);
lean_dec(v___y_1444_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1464_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1455_ = lean_array_uget_borrowed(v_as_1440_, v_i_1441_);
v___x_1456_ = lean_box(0);
lean_inc(v___x_1455_);
v___x_1457_ = lean_array_push(v_log_1447_, v___x_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1457_);
v___x_1459_ = v___x_1453_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_trace_1450_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_buildTime_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1463_, sizeof(void*)*3, v_action_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1463_, sizeof(void*)*3 + 1, v_wantsRebuild_1449_);
v___x_1459_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
size_t v___x_1460_; size_t v___x_1461_; 
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_add(v_i_1441_, v___x_1460_);
v_i_1441_ = v___x_1461_;
v_b_1443_ = v___x_1456_;
v___y_1444_ = v___x_1459_;
goto _start;
}
}
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1443_);
lean_ctor_set(v___x_1465_, 1, v___y_1444_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1466_, lean_object* v_i_1467_, lean_object* v_stop_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
size_t v_i_boxed_1472_; size_t v_stop_boxed_1473_; lean_object* v_res_1474_; 
v_i_boxed_1472_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_stop_boxed_1473_ = lean_unbox_usize(v_stop_1468_);
lean_dec(v_stop_1468_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1466_, v_i_boxed_1472_, v_stop_boxed_1473_, v_b_1469_, v___y_1470_);
lean_dec_ref(v_as_1466_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_array_get_size(v_log_1475_);
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v_a_1481_);
return v___x_1487_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_le(v___x_1484_, v___x_1484_);
if (v___x_1488_ == 0)
{
if (v___x_1486_ == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1485_);
lean_ctor_set(v___x_1489_, 1, v_a_1481_);
return v___x_1489_;
}
else
{
size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = lean_usize_of_nat(v___x_1484_);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1475_, v___x_1490_, v___x_1491_, v___x_1485_, v_a_1481_);
return v___x_1492_;
}
}
else
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = lean_usize_of_nat(v___x_1484_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1475_, v___x_1493_, v___x_1494_, v___x_1485_, v_a_1481_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec_ref(v_log_1496_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1505_, size_t v_i_1506_, size_t v_stop_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1505_, v_i_1506_, v_stop_1507_, v_b_1508_, v___y_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1517_, lean_object* v_i_1518_, lean_object* v_stop_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_i_boxed_1528_; size_t v_stop_boxed_1529_; lean_object* v_res_1530_; 
v_i_boxed_1528_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_stop_boxed_1529_ = lean_unbox_usize(v_stop_1519_);
lean_dec(v_stop_1519_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1517_, v_i_boxed_1528_, v_stop_boxed_1529_, v_b_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_as_1517_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_info_1533_, lean_object* v_depTrace_1534_, lean_object* v_savedTrace_1535_, lean_object* v_oldTrace_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
if (lean_obj_tag(v_savedTrace_1535_) == 2)
{
lean_object* v_data_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1594_; 
v_data_1544_ = lean_ctor_get(v_savedTrace_1535_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_savedTrace_1535_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1546_ = v_savedTrace_1535_;
v_isShared_1547_ = v_isSharedCheck_1594_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_data_1544_);
lean_dec(v_savedTrace_1535_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1594_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint64_t v_depHash_1548_; lean_object* v_log_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v_depHash_1548_ = lean_ctor_get_uint64(v_data_1544_, sizeof(void*)*3);
v_log_1549_ = lean_ctor_get(v_data_1544_, 2);
lean_inc_ref(v_log_1549_);
lean_dec_ref(v_data_1544_);
v___x_1550_ = lean_box_uint64(v_depHash_1548_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1550_);
v___x_1552_ = v___x_1546_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1592_; 
v___x_1553_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1531_, v_inst_1532_, v_info_1533_, v_depTrace_1534_, v___x_1552_, v_oldTrace_1536_, v_a_1541_, v_a_1542_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1557_ = v___x_1553_;
v_isShared_1558_ = v_isSharedCheck_1592_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1592_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___y_1560_; uint8_t v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = 0;
v___x_1565_ = lean_unbox(v_a_1554_);
v___x_1566_ = l_Lake_instDecidableEqOutputStatus(v___x_1565_, v___x_1564_);
if (v___x_1566_ == 0)
{
lean_object* v_log_1567_; uint8_t v_action_1568_; uint8_t v_wantsRebuild_1569_; lean_object* v_trace_1570_; lean_object* v_buildTime_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1591_; 
v_log_1567_ = lean_ctor_get(v_a_1555_, 0);
v_action_1568_ = lean_ctor_get_uint8(v_a_1555_, sizeof(void*)*3);
v_wantsRebuild_1569_ = lean_ctor_get_uint8(v_a_1555_, sizeof(void*)*3 + 1);
v_trace_1570_ = lean_ctor_get(v_a_1555_, 1);
v_buildTime_1571_ = lean_ctor_get(v_a_1555_, 2);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_a_1555_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1573_ = v_a_1555_;
v_isShared_1574_ = v_isSharedCheck_1591_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_buildTime_1571_);
lean_inc(v_trace_1570_);
lean_inc(v_log_1567_);
lean_dec(v_a_1555_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1591_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = 2;
v___x_1576_ = l_Lake_JobAction_merge(v_action_1568_, v___x_1575_);
if (v_isShared_1574_ == 0)
{
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_log_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_trace_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_buildTime_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*3 + 1, v_wantsRebuild_1569_);
v___x_1578_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; 
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*3, v___x_1576_);
v___x_1579_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1549_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v___x_1578_);
lean_dec_ref(v_log_1549_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 1);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 2);
v___y_1560_ = v_a_1580_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1557_);
lean_dec(v_a_1554_);
v_a_1581_ = lean_ctor_get(v___x_1579_, 0);
v_a_1582_ = lean_ctor_get(v___x_1579_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1579_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_inc(v_a_1581_);
lean_dec(v___x_1579_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1549_);
v___y_1560_ = v_a_1555_;
goto v___jp_1559_;
}
v___jp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v___y_1560_);
v___x_1562_ = v___x_1557_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1554_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___y_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1595_; uint8_t v_oldMode_1596_; 
lean_dec(v_savedTrace_1535_);
lean_dec_ref(v_inst_1531_);
v_toBuildConfig_1595_ = lean_ctor_get(v_a_1541_, 0);
v_oldMode_1596_ = lean_ctor_get_uint8(v_toBuildConfig_1595_, sizeof(void*)*4);
if (v_oldMode_1596_ == 0)
{
uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_info_1533_);
lean_dec_ref(v_inst_1532_);
v___x_1597_ = 0;
v___x_1598_ = lean_box(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v_a_1542_);
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1532_, v_info_1533_, v_oldTrace_1536_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = 0;
v___x_1602_ = lean_box(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_a_1542_);
return v___x_1603_;
}
else
{
uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = 1;
v___x_1605_ = lean_box(v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v_a_1542_);
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_info_1609_, lean_object* v_depTrace_1610_, lean_object* v_savedTrace_1611_, lean_object* v_oldTrace_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1607_, v_inst_1608_, v_info_1609_, v_depTrace_1610_, v_savedTrace_1611_, v_oldTrace_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec_ref(v_oldTrace_1612_);
lean_dec_ref(v_depTrace_1610_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_info_1624_, lean_object* v_depTrace_1625_, lean_object* v_savedTrace_1626_, lean_object* v_oldTrace_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1622_, v_inst_1623_, v_info_1624_, v_depTrace_1625_, v_savedTrace_1626_, v_oldTrace_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_info_1639_, lean_object* v_depTrace_1640_, lean_object* v_savedTrace_1641_, lean_object* v_oldTrace_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1636_, v_inst_1637_, v_inst_1638_, v_info_1639_, v_depTrace_1640_, v_savedTrace_1641_, v_oldTrace_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec_ref(v_oldTrace_1642_);
lean_dec_ref(v_depTrace_1640_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_info_1653_, lean_object* v_depTrace_1654_, lean_object* v_savedTrace_1655_, lean_object* v_oldTrace_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1651_, v_inst_1652_, v_info_1653_, v_depTrace_1654_, v_savedTrace_1655_, v_oldTrace_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1683_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_a_1666_ = lean_ctor_get(v___x_1664_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1668_ = v___x_1664_;
v_isShared_1669_ = v_isSharedCheck_1683_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1683_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v___x_1670_; uint8_t v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = 0;
v___x_1671_ = lean_unbox(v_a_1665_);
lean_dec(v_a_1665_);
v___x_1672_ = l_Lake_instDecidableEqOutputStatus(v___x_1671_, v___x_1670_);
if (v___x_1672_ == 0)
{
uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1673_ = 1;
v___x_1674_ = lean_box(v___x_1673_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1674_);
v___x_1676_ = v___x_1668_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_a_1666_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
else
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = 0;
v___x_1679_ = lean_box(v___x_1678_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1679_);
v___x_1681_ = v___x_1668_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1666_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1684_ = lean_ctor_get(v___x_1664_, 0);
v_a_1685_ = lean_ctor_get(v___x_1664_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1664_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_inc(v_a_1684_);
lean_dec(v___x_1664_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_info_1695_, lean_object* v_depTrace_1696_, lean_object* v_savedTrace_1697_, lean_object* v_oldTrace_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1693_, v_inst_1694_, v_info_1695_, v_depTrace_1696_, v_savedTrace_1697_, v_oldTrace_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v_oldTrace_1698_);
lean_dec_ref(v_depTrace_1696_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_info_1710_, lean_object* v_depTrace_1711_, lean_object* v_savedTrace_1712_, lean_object* v_oldTrace_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1708_, v_inst_1709_, v_info_1710_, v_depTrace_1711_, v_savedTrace_1712_, v_oldTrace_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1740_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_a_1723_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1740_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1740_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = 0;
v___x_1728_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1729_ = l_Lake_instDecidableEqOutputStatus(v___x_1728_, v___x_1727_);
if (v___x_1729_ == 0)
{
uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = 1;
v___x_1731_ = lean_box(v___x_1730_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1731_);
v___x_1733_ = v___x_1725_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_a_1723_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = 0;
v___x_1736_ = lean_box(v___x_1735_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1736_);
v___x_1738_ = v___x_1725_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1723_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1741_ = lean_ctor_get(v___x_1721_, 0);
v_a_1742_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1721_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_inc(v_a_1741_);
lean_dec(v___x_1721_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_info_1753_, lean_object* v_depTrace_1754_, lean_object* v_savedTrace_1755_, lean_object* v_oldTrace_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1750_, v_inst_1751_, v_inst_1752_, v_info_1753_, v_depTrace_1754_, v_savedTrace_1755_, v_oldTrace_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec_ref(v_oldTrace_1756_);
lean_dec_ref(v_depTrace_1754_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t v_inputHash_1765_, lean_object* v_self_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___y_1770_; 
if (lean_obj_tag(v_self_1766_) == 2)
{
lean_object* v_data_1788_; uint64_t v_depHash_1789_; lean_object* v_log_1790_; uint8_t v_synthetic_1791_; uint8_t v___x_1792_; lean_object* v___y_1794_; lean_object* v___y_1798_; 
v_data_1788_ = lean_ctor_get(v_self_1766_, 0);
v_depHash_1789_ = lean_ctor_get_uint64(v_data_1788_, sizeof(void*)*3);
v_log_1790_ = lean_ctor_get(v_data_1788_, 2);
v_synthetic_1791_ = lean_ctor_get_uint8(v_data_1788_, sizeof(void*)*3 + 8);
v___x_1792_ = lean_uint64_dec_eq(v_depHash_1789_, v_inputHash_1765_);
if (v___x_1792_ == 0)
{
v___y_1770_ = v_a_1767_;
goto v___jp_1769_;
}
else
{
if (v_synthetic_1791_ == 0)
{
goto v___jp_1809_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_get_size(v_log_1790_);
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
goto v___jp_1809_;
}
else
{
lean_object* v_log_1838_; uint8_t v_action_1839_; uint8_t v_wantsRebuild_1840_; lean_object* v_trace_1841_; lean_object* v_buildTime_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v_log_1838_ = lean_ctor_get(v_a_1767_, 0);
v_action_1839_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1840_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1841_ = lean_ctor_get(v_a_1767_, 1);
v_buildTime_1842_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v_a_1767_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_buildTime_1842_);
lean_inc(v_trace_1841_);
lean_inc(v_log_1838_);
lean_dec(v_a_1767_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
uint8_t v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = 1;
v___x_1847_ = l_Lake_JobAction_merge(v_action_1839_, v___x_1846_);
if (v_isShared_1845_ == 0)
{
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_log_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_trace_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_buildTime_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*3 + 1, v_wantsRebuild_1840_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*3, v___x_1847_);
v___y_1794_ = v___x_1849_;
goto v___jp_1793_;
}
}
}
}
}
v___jp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_box(v___x_1792_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___y_1794_);
return v___x_1796_;
}
v___jp_1797_:
{
if (lean_obj_tag(v___y_1798_) == 0)
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___y_1798_, 1);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___y_1798_, 2);
v___y_1794_ = v_a_1799_;
goto v___jp_1793_;
}
else
{
lean_object* v_a_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1800_ = lean_ctor_get(v___y_1798_, 0);
v_a_1801_ = lean_ctor_get(v___y_1798_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___y_1798_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___y_1798_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_inc(v_a_1800_);
lean_dec(v___y_1798_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1800_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
v___jp_1809_:
{
lean_object* v_log_1810_; uint8_t v_action_1811_; uint8_t v_wantsRebuild_1812_; lean_object* v_trace_1813_; lean_object* v_buildTime_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1834_; 
v_log_1810_ = lean_ctor_get(v_a_1767_, 0);
v_action_1811_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1812_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1813_ = lean_ctor_get(v_a_1767_, 1);
v_buildTime_1814_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1816_ = v_a_1767_;
v_isShared_1817_ = v_isSharedCheck_1834_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_buildTime_1814_);
lean_inc(v_trace_1813_);
lean_inc(v_log_1810_);
lean_dec(v_a_1767_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1834_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
uint8_t v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = 2;
v___x_1819_ = l_Lake_JobAction_merge(v_action_1811_, v___x_1818_);
if (v_isShared_1817_ == 0)
{
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_log_1810_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_trace_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_buildTime_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*3 + 1, v_wantsRebuild_1812_);
v___x_1821_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*3, v___x_1819_);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_array_get_size(v_log_1790_);
v___x_1824_ = lean_nat_dec_lt(v___x_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
v___y_1794_ = v___x_1821_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_nat_dec_le(v___x_1823_, v___x_1823_);
if (v___x_1826_ == 0)
{
if (v___x_1824_ == 0)
{
v___y_1794_ = v___x_1821_;
goto v___jp_1793_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1823_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1790_, v___x_1827_, v___x_1828_, v___x_1825_, v___x_1821_);
v___y_1798_ = v___x_1829_;
goto v___jp_1797_;
}
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1823_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1790_, v___x_1830_, v___x_1831_, v___x_1825_, v___x_1821_);
v___y_1798_ = v___x_1832_;
goto v___jp_1797_;
}
}
}
}
}
}
else
{
v___y_1770_ = v_a_1767_;
goto v___jp_1769_;
}
v___jp_1769_:
{
lean_object* v_log_1771_; uint8_t v_action_1772_; uint8_t v_wantsRebuild_1773_; lean_object* v_trace_1774_; lean_object* v_buildTime_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1787_; 
v_log_1771_ = lean_ctor_get(v___y_1770_, 0);
v_action_1772_ = lean_ctor_get_uint8(v___y_1770_, sizeof(void*)*3);
v_wantsRebuild_1773_ = lean_ctor_get_uint8(v___y_1770_, sizeof(void*)*3 + 1);
v_trace_1774_ = lean_ctor_get(v___y_1770_, 1);
v_buildTime_1775_ = lean_ctor_get(v___y_1770_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___y_1770_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1777_ = v___y_1770_;
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_buildTime_1775_);
lean_inc(v_trace_1774_);
lean_inc(v_log_1771_);
lean_dec(v___y_1770_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
uint8_t v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = 1;
v___x_1780_ = l_Lake_JobAction_merge(v_action_1772_, v___x_1779_);
if (v_isShared_1778_ == 0)
{
v___x_1782_ = v___x_1777_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_log_1771_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_trace_1774_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_buildTime_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 1, v_wantsRebuild_1773_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3, v___x_1780_);
v___x_1783_ = 0;
v___x_1784_ = lean_box(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1782_);
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object* v_inputHash_1852_, lean_object* v_self_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
uint64_t v_inputHash_boxed_1856_; lean_object* v_res_1857_; 
v_inputHash_boxed_1856_ = lean_unbox_uint64(v_inputHash_1852_);
lean_dec_ref(v_inputHash_1852_);
v_res_1857_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_boxed_1856_, v_self_1853_, v_a_1854_);
lean_dec(v_self_1853_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t v_inputHash_1858_, lean_object* v_self_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1858_, v_self_1859_, v_a_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object* v_inputHash_1868_, lean_object* v_self_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
uint64_t v_inputHash_boxed_1877_; lean_object* v_res_1878_; 
v_inputHash_boxed_1877_ = lean_unbox_uint64(v_inputHash_1868_);
lean_dec_ref(v_inputHash_1868_);
v_res_1878_ = l_Lake_SavedTrace_replayCachedIfUpToDate(v_inputHash_boxed_1877_, v_self_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_self_1869_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1879_, lean_object* v_self_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1879_, v_self_1880_, v_a_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1884_, lean_object* v_self_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
uint64_t v_inputHash_boxed_1888_; lean_object* v_res_1889_; 
v_inputHash_boxed_1888_ = lean_unbox_uint64(v_inputHash_1884_);
lean_dec_ref(v_inputHash_1884_);
v_res_1889_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1888_, v_self_1885_, v_a_1886_);
lean_dec(v_self_1885_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1890_, lean_object* v_self_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1890_, v_self_1891_, v_a_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1900_, lean_object* v_self_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
uint64_t v_inputHash_boxed_1909_; lean_object* v_res_1910_; 
v_inputHash_boxed_1909_ = lean_unbox_uint64(v_inputHash_1900_);
lean_dec_ref(v_inputHash_1900_);
v_res_1910_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1909_, v_self_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_self_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1916_){
_start:
{
lean_object* v_descr_1917_; uint64_t v_hash_1918_; lean_object* v_ext_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_descr_1917_ = lean_ctor_get(v_x_1916_, 0);
v_hash_1918_ = lean_ctor_get_uint64(v_descr_1917_, sizeof(void*)*1);
v_ext_1919_ = lean_ctor_get(v_descr_1917_, 0);
v___x_1920_ = lean_string_utf8_byte_size(v_ext_1919_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = lean_nat_dec_eq(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1923_ = l_Lake_lowerHexUInt64(v_hash_1918_);
v___x_1924_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1925_ = lean_string_append(v___x_1923_, v___x_1924_);
v___x_1926_ = lean_string_append(v___x_1925_, v_ext_1919_);
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = l_Lake_lowerHexUInt64(v_hash_1918_);
v___x_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1930_);
lean_dec_ref(v_x_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1934_, lean_object* v_a_x3f_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_log_1939_; uint8_t v_action_1940_; uint8_t v_wantsRebuild_1941_; lean_object* v_trace_1942_; lean_object* v_buildTime_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1954_; 
v___x_1938_ = lean_io_mono_ms_now();
v_log_1939_ = lean_ctor_get(v___y_1936_, 0);
v_action_1940_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3);
v_wantsRebuild_1941_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 1);
v_trace_1942_ = lean_ctor_get(v___y_1936_, 1);
v_buildTime_1943_ = lean_ctor_get(v___y_1936_, 2);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1945_ = v___y_1936_;
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_buildTime_1943_);
lean_inc(v_trace_1942_);
lean_inc(v_log_1939_);
lean_dec(v___y_1936_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1947_ = lean_nat_sub(v___x_1938_, v_val_1934_);
lean_dec(v___x_1938_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_nat_add(v_buildTime_1943_, v___x_1947_);
lean_dec(v___x_1947_);
lean_dec(v_buildTime_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 2, v___x_1949_);
v___x_1951_ = v___x_1945_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_log_1939_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_trace_1942_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3, v_action_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3 + 1, v_wantsRebuild_1941_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1948_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
return v___x_1952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1955_, lean_object* v_a_x3f_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lake_buildAction___redArg___lam__0(v_val_1955_, v_a_x3f_1956_, v___y_1957_);
lean_dec(v_a_x3f_1956_);
lean_dec(v_val_1955_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1965_, lean_object* v_depTrace_1966_, lean_object* v_traceFile_1967_, lean_object* v_build_1968_, uint8_t v_action_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_a_1978_; lean_object* v_a_1979_; lean_object* v_log_1982_; uint8_t v_action_1983_; uint8_t v_wantsRebuild_1984_; lean_object* v_trace_1985_; lean_object* v_buildTime_1986_; lean_object* v_toBuildConfig_1992_; lean_object* v_log_1993_; uint8_t v_action_1994_; uint8_t v_wantsRebuild_1995_; lean_object* v_trace_1996_; lean_object* v_buildTime_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2103_; 
v_toBuildConfig_1992_ = lean_ctor_get(v_a_1974_, 0);
v_log_1993_ = lean_ctor_get(v_a_1975_, 0);
v_action_1994_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*3);
v_wantsRebuild_1995_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*3 + 1);
v_trace_1996_ = lean_ctor_get(v_a_1975_, 1);
v_buildTime_1997_ = lean_ctor_get(v_a_1975_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_1975_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_1999_ = v_a_1975_;
v_isShared_2000_ = v_isSharedCheck_2103_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_buildTime_1997_);
lean_inc(v_trace_1996_);
lean_inc(v_log_1993_);
lean_dec(v_a_1975_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2103_;
goto v_resetjp_1998_;
}
v___jp_1977_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1978_);
lean_ctor_set(v___x_1980_, 1, v_a_1979_);
return v___x_1980_;
}
v___jp_1981_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1988_ = lean_array_get_size(v_log_1982_);
v___x_1989_ = lean_array_push(v_log_1982_, v___x_1987_);
v___x_1990_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_trace_1985_);
lean_ctor_set(v___x_1990_, 2, v_buildTime_1986_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v_action_1983_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3 + 1, v_wantsRebuild_1984_);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
v_resetjp_1998_:
{
uint8_t v_noBuild_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_noBuild_2001_ = lean_ctor_get_uint8(v_toBuildConfig_1992_, sizeof(void*)*4 + 2);
v___x_2002_ = l_Lake_JobAction_merge(v_action_1994_, v_action_1969_);
v___x_2003_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1967_);
v___x_2004_ = l_System_FilePath_addExtension(v_traceFile_1967_, v___x_2003_);
if (v_noBuild_2001_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1993_);
if (v_isShared_2000_ == 0)
{
v___x_2007_ = v___x_1999_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_log_1993_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_trace_1996_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_buildTime_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2087_, sizeof(void*)*3 + 1, v_wantsRebuild_1995_);
v___x_2007_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v_a_2010_; lean_object* v_a_2011_; 
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3, v___x_2002_);
lean_inc_ref(v_a_1974_);
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
v___x_2008_ = lean_apply_7(v_build_1968_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v___x_2007_, lean_box(0));
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2015_; lean_object* v_a_2016_; lean_object* v_log_2017_; uint8_t v_action_2018_; uint8_t v_wantsRebuild_2019_; lean_object* v_trace_2020_; lean_object* v_buildTime_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2015_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2015_);
v_a_2016_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_n(v_a_2016_, 2);
lean_dec_ref_known(v___x_2008_, 2);
v_log_2017_ = lean_ctor_get(v_a_2015_, 0);
v_action_2018_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*3);
v_wantsRebuild_2019_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*3 + 1);
v_trace_2020_ = lean_ctor_get(v_a_2015_, 1);
v_buildTime_2021_ = lean_ctor_get(v_a_2015_, 2);
v___x_2022_ = lean_array_get_size(v_log_1993_);
lean_dec_ref(v_log_1993_);
v___x_2023_ = lean_array_get_size(v_log_2017_);
v___x_2024_ = l_Array_extract___redArg(v_log_2017_, v___x_2022_, v___x_2023_);
v___x_2025_ = lean_apply_1(v_inst_1965_, v_a_2016_);
v___x_2026_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1966_, v___x_2025_, v___x_2024_);
v___x_2027_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1967_, v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2068_; 
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2069_);
v___x_2029_ = v___x_2027_;
v_isShared_2030_ = v_isSharedCheck_2068_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v___x_2027_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2068_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lake_removeFileIfExists(v___x_2004_);
lean_dec_ref(v___x_2004_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2052_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
lean_inc(v_a_2016_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v_a_2016_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2016_);
v___x_2036_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 1);
lean_ctor_set(v___x_2029_, 0, v___x_2036_);
v___x_2038_ = v___x_2029_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v___x_2039_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2038_, v_a_2015_);
lean_dec_ref(v___x_2038_);
lean_dec(v___x_2005_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2048_);
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_a_2016_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2016_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
else
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2064_; 
lean_inc(v_buildTime_2021_);
lean_inc_ref(v_trace_2020_);
lean_inc_ref(v_log_2017_);
lean_del_object(v___x_2029_);
lean_dec(v_a_2016_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; 
v_unused_2065_ = lean_ctor_get(v_a_2015_, 2);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_a_2015_, 0);
lean_dec(v_unused_2067_);
v___x_2054_ = v_a_2015_;
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v_a_2015_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_a_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v_a_2056_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2057_ = lean_io_error_to_string(v_a_2056_);
v___x_2058_ = 3;
v___x_2059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*1, v___x_2058_);
v___x_2060_ = lean_array_push(v_log_2017_, v___x_2059_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2060_);
v___x_2062_ = v___x_2054_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_trace_2020_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_buildTime_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_action_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 1, v_wantsRebuild_2019_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_2010_ = v___x_2023_;
v_a_2011_ = v___x_2062_;
goto v___jp_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_buildTime_2021_);
lean_inc_ref(v_trace_2020_);
lean_inc_ref(v_log_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2004_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2082_ = lean_ctor_get(v_a_2015_, 2);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_a_2015_, 0);
lean_dec(v_unused_2084_);
v___x_2071_ = v_a_2015_;
v_isShared_2072_ = v_isSharedCheck_2081_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_a_2015_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2081_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_a_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v_a_2073_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2074_ = lean_io_error_to_string(v_a_2073_);
v___x_2075_ = 3;
v___x_2076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1, v___x_2075_);
v___x_2077_ = lean_array_push(v_log_2017_, v___x_2076_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2077_);
v___x_2079_ = v___x_2071_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_trace_2020_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_buildTime_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3, v_action_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3 + 1, v_wantsRebuild_2019_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v_a_2010_ = v___x_2023_;
v_a_2011_ = v___x_2079_;
goto v___jp_2009_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v_a_2086_; 
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_log_1993_);
lean_dec_ref(v_traceFile_1967_);
lean_dec_ref(v_inst_1965_);
v_a_2085_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2085_);
v_a_2086_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2008_, 2);
v_a_2010_ = v_a_2085_;
v_a_2011_ = v_a_2086_;
goto v___jp_2009_;
}
v___jp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_a_2014_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2012_, v_a_2011_);
lean_dec(v___x_2005_);
v_a_2014_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v_a_1978_ = v_a_2010_;
v_a_1979_ = v_a_2014_;
goto v___jp_1977_;
}
}
}
else
{
uint8_t v___x_2088_; 
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_build_1968_);
lean_dec_ref(v_inst_1965_);
v___x_2088_ = l_System_FilePath_pathExists(v_traceFile_1967_);
lean_dec_ref(v_traceFile_1967_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2004_);
lean_del_object(v___x_1999_);
v_log_1982_ = v_log_1993_;
v_action_1983_ = v___x_2002_;
v_wantsRebuild_1984_ = v_noBuild_2001_;
v_trace_1985_ = v_trace_1996_;
v_buildTime_1986_ = v_buildTime_1997_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2091_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1966_, v___x_2089_, v___x_2090_);
v___x_2092_ = l_Lake_BuildMetadata_writeFile(v___x_2004_, v___x_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
lean_del_object(v___x_1999_);
v_log_1982_ = v_log_1993_;
v_action_1983_ = v___x_2002_;
v_wantsRebuild_1984_ = v_noBuild_2001_;
v_trace_1985_ = v_trace_1996_;
v_buildTime_1986_ = v_buildTime_1997_;
goto v___jp_1981_;
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_io_error_to_string(v_a_2093_);
v___x_2095_ = 3;
v___x_2096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*1, v___x_2095_);
v___x_2097_ = lean_array_get_size(v_log_1993_);
v___x_2098_ = lean_array_push(v_log_1993_, v___x_2096_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2098_);
v___x_2100_ = v___x_1999_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_trace_1996_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_buildTime_1997_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3, v___x_2002_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3 + 1, v_noBuild_2001_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2097_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
return v___x_2101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2104_, lean_object* v_depTrace_2105_, lean_object* v_traceFile_2106_, lean_object* v_build_2107_, lean_object* v_action_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
uint8_t v_action_boxed_2116_; lean_object* v_res_2117_; 
v_action_boxed_2116_ = lean_unbox(v_action_2108_);
v_res_2117_ = l_Lake_buildAction___redArg(v_inst_2104_, v_depTrace_2105_, v_traceFile_2106_, v_build_2107_, v_action_boxed_2116_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_depTrace_2105_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2118_, lean_object* v_inst_2119_, lean_object* v_depTrace_2120_, lean_object* v_traceFile_2121_, lean_object* v_build_2122_, uint8_t v_action_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lake_buildAction___redArg(v_inst_2119_, v_depTrace_2120_, v_traceFile_2121_, v_build_2122_, v_action_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_inst_2133_, lean_object* v_depTrace_2134_, lean_object* v_traceFile_2135_, lean_object* v_build_2136_, lean_object* v_action_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
uint8_t v_action_boxed_2145_; lean_object* v_res_2146_; 
v_action_boxed_2145_ = lean_unbox(v_action_2137_);
v_res_2146_ = l_Lake_buildAction(v_00_u03b1_2132_, v_inst_2133_, v_depTrace_2134_, v_traceFile_2135_, v_build_2136_, v_action_boxed_2145_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_depTrace_2134_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_info_2149_, lean_object* v_depTrace_2150_, lean_object* v_traceFile_2151_, lean_object* v_build_2152_, uint8_t v_action_2153_, lean_object* v_oldTrace_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_log_2162_; uint8_t v_action_2163_; uint8_t v_wantsRebuild_2164_; lean_object* v_trace_2165_; lean_object* v_buildTime_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2234_; 
v_log_2162_ = lean_ctor_get(v_a_2160_, 0);
v_action_2163_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3);
v_wantsRebuild_2164_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3 + 1);
v_trace_2165_ = lean_ctor_get(v_a_2160_, 1);
v_buildTime_2166_ = lean_ctor_get(v_a_2160_, 2);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_a_2160_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2168_ = v_a_2160_;
v_isShared_2169_ = v_isSharedCheck_2234_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_buildTime_2166_);
lean_inc(v_trace_2165_);
lean_inc(v_log_2162_);
lean_dec(v_a_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2234_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; 
lean_inc_ref(v_traceFile_2151_);
v___x_2170_ = l_Lake_readTraceFile(v_traceFile_2151_, v_log_2162_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
v_a_2172_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2170_, 2);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v_a_2172_);
v___x_2174_ = v___x_2168_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2172_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_trace_2165_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_buildTime_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*3, v_action_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*3 + 1, v_wantsRebuild_2164_);
v___x_2174_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2147_, v_inst_2148_, v_info_2149_, v_depTrace_2150_, v_a_2171_, v_oldTrace_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v___x_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2211_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2179_ = v___x_2175_;
v_isShared_2180_ = v_isSharedCheck_2211_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2211_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; uint8_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = 0;
v___x_2182_ = lean_unbox(v_a_2176_);
lean_dec(v_a_2176_);
v___x_2183_ = l_Lake_instDecidableEqOutputStatus(v___x_2182_, v___x_2181_);
if (v___x_2183_ == 0)
{
uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
v___x_2184_ = 1;
v___x_2185_ = lean_box(v___x_2184_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2185_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2177_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
else
{
lean_object* v___f_2189_; lean_object* v___x_2190_; 
lean_del_object(v___x_2179_);
v___f_2189_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2190_ = l_Lake_buildAction___redArg(v___f_2189_, v_depTrace_2150_, v_traceFile_2151_, v_build_2152_, v_action_2153_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2177_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2200_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2201_);
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = 0;
v___x_2196_ = lean_box(v___x_2195_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_a_2191_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_a_2202_ = lean_ctor_get(v___x_2190_, 0);
v_a_2203_ = lean_ctor_get(v___x_2190_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2190_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_inc(v_a_2202_);
lean_dec(v___x_2190_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
v_a_2212_ = lean_ctor_get(v___x_2175_, 0);
v_a_2213_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2175_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_inc(v_a_2212_);
lean_dec(v___x_2175_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2212_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
lean_dec(v_info_2149_);
lean_dec_ref(v_inst_2148_);
lean_dec_ref(v_inst_2147_);
v_a_2222_ = lean_ctor_get(v___x_2170_, 0);
v_a_2223_ = lean_ctor_get(v___x_2170_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2225_ = v___x_2170_;
v_isShared_2226_ = v_isSharedCheck_2233_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_inc(v_a_2222_);
lean_dec(v___x_2170_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2233_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v_a_2223_);
v___x_2228_ = v___x_2168_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2223_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_trace_2165_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_buildTime_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3, v_action_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 1, v_wantsRebuild_2164_);
v___x_2228_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2230_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2222_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_info_2237_, lean_object* v_depTrace_2238_, lean_object* v_traceFile_2239_, lean_object* v_build_2240_, lean_object* v_action_2241_, lean_object* v_oldTrace_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
uint8_t v_action_boxed_2250_; lean_object* v_res_2251_; 
v_action_boxed_2250_ = lean_unbox(v_action_2241_);
v_res_2251_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2235_, v_inst_2236_, v_info_2237_, v_depTrace_2238_, v_traceFile_2239_, v_build_2240_, v_action_boxed_2250_, v_oldTrace_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_oldTrace_2242_);
lean_dec_ref(v_depTrace_2238_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_info_2255_, lean_object* v_depTrace_2256_, lean_object* v_traceFile_2257_, lean_object* v_build_2258_, uint8_t v_action_2259_, lean_object* v_oldTrace_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_log_2268_; uint8_t v_action_2269_; uint8_t v_wantsRebuild_2270_; lean_object* v_trace_2271_; lean_object* v_buildTime_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2340_; 
v_log_2268_ = lean_ctor_get(v_a_2266_, 0);
v_action_2269_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*3);
v_wantsRebuild_2270_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*3 + 1);
v_trace_2271_ = lean_ctor_get(v_a_2266_, 1);
v_buildTime_2272_ = lean_ctor_get(v_a_2266_, 2);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_a_2266_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2274_ = v_a_2266_;
v_isShared_2275_ = v_isSharedCheck_2340_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_buildTime_2272_);
lean_inc(v_trace_2271_);
lean_inc(v_log_2268_);
lean_dec(v_a_2266_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2340_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; 
lean_inc_ref(v_traceFile_2257_);
v___x_2276_ = l_Lake_readTraceFile(v_traceFile_2257_, v_log_2268_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
v_a_2278_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2276_, 2);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v_a_2278_);
v___x_2280_ = v___x_2274_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2278_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_trace_2271_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_buildTime_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3, v_action_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3 + 1, v_wantsRebuild_2270_);
v___x_2280_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2253_, v_inst_2254_, v_info_2255_, v_depTrace_2256_, v_a_2277_, v_oldTrace_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v___x_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2317_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_a_2283_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2285_ = v___x_2281_;
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2317_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
uint8_t v___x_2287_; uint8_t v___x_2288_; uint8_t v___x_2289_; 
v___x_2287_ = 0;
v___x_2288_ = lean_unbox(v_a_2282_);
lean_dec(v_a_2282_);
v___x_2289_ = l_Lake_instDecidableEqOutputStatus(v___x_2288_, v___x_2287_);
if (v___x_2289_ == 0)
{
uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_build_2258_);
lean_dec_ref(v_traceFile_2257_);
v___x_2290_ = 1;
v___x_2291_ = lean_box(v___x_2290_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2291_);
v___x_2293_ = v___x_2285_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_a_2283_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v___f_2295_; lean_object* v___x_2296_; 
lean_del_object(v___x_2285_);
v___f_2295_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2296_ = l_Lake_buildAction___redArg(v___f_2295_, v_depTrace_2256_, v_traceFile_2257_, v_build_2258_, v_action_2259_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2283_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2296_, 0);
lean_dec(v_unused_2307_);
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = 0;
v___x_2302_ = lean_box(v___x_2301_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2302_);
v___x_2304_ = v___x_2299_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_a_2297_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2308_ = lean_ctor_get(v___x_2296_, 0);
v_a_2309_ = lean_ctor_get(v___x_2296_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2296_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_inc(v_a_2308_);
lean_dec(v___x_2296_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2308_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_build_2258_);
lean_dec_ref(v_traceFile_2257_);
v_a_2318_ = lean_ctor_get(v___x_2281_, 0);
v_a_2319_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2281_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_inc(v_a_2318_);
lean_dec(v___x_2281_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2318_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_build_2258_);
lean_dec_ref(v_traceFile_2257_);
lean_dec(v_info_2255_);
lean_dec_ref(v_inst_2254_);
lean_dec_ref(v_inst_2253_);
v_a_2328_ = lean_ctor_get(v___x_2276_, 0);
v_a_2329_ = lean_ctor_get(v___x_2276_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2331_ = v___x_2276_;
v_isShared_2332_ = v_isSharedCheck_2339_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_inc(v_a_2328_);
lean_dec(v___x_2276_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2339_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v_a_2329_);
v___x_2334_ = v___x_2274_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2329_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_trace_2271_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_buildTime_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*3, v_action_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*3 + 1, v_wantsRebuild_2270_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2334_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2328_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_info_2344_, lean_object* v_depTrace_2345_, lean_object* v_traceFile_2346_, lean_object* v_build_2347_, lean_object* v_action_2348_, lean_object* v_oldTrace_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
uint8_t v_action_boxed_2357_; lean_object* v_res_2358_; 
v_action_boxed_2357_ = lean_unbox(v_action_2348_);
v_res_2358_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2341_, v_inst_2342_, v_inst_2343_, v_info_2344_, v_depTrace_2345_, v_traceFile_2346_, v_build_2347_, v_action_boxed_2357_, v_oldTrace_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_oldTrace_2349_);
lean_dec_ref(v_depTrace_2345_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_info_2361_, lean_object* v_depTrace_2362_, lean_object* v_traceFile_2363_, lean_object* v_build_2364_, uint8_t v_action_2365_, lean_object* v_oldTrace_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_a_2375_; lean_object* v_a_2376_; lean_object* v_log_2378_; uint8_t v_action_2379_; uint8_t v_wantsRebuild_2380_; lean_object* v_trace_2381_; lean_object* v_buildTime_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2420_; 
v_log_2378_ = lean_ctor_get(v_a_2372_, 0);
v_action_2379_ = lean_ctor_get_uint8(v_a_2372_, sizeof(void*)*3);
v_wantsRebuild_2380_ = lean_ctor_get_uint8(v_a_2372_, sizeof(void*)*3 + 1);
v_trace_2381_ = lean_ctor_get(v_a_2372_, 1);
v_buildTime_2382_ = lean_ctor_get(v_a_2372_, 2);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_a_2372_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2384_ = v_a_2372_;
v_isShared_2385_ = v_isSharedCheck_2420_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_buildTime_2382_);
lean_inc(v_trace_2381_);
lean_inc(v_log_2378_);
lean_dec(v_a_2372_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2420_;
goto v_resetjp_2383_;
}
v___jp_2374_:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2375_);
lean_ctor_set(v___x_2377_, 1, v_a_2376_);
return v___x_2377_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; 
lean_inc_ref(v_traceFile_2363_);
v___x_2386_ = l_Lake_readTraceFile(v_traceFile_2363_, v_log_2378_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
v_a_2388_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2386_, 2);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_a_2388_);
v___x_2390_ = v___x_2384_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2388_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_trace_2381_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_buildTime_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*3, v_action_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*3 + 1, v_wantsRebuild_2380_);
v___x_2390_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2359_, v_inst_2360_, v_info_2361_, v_depTrace_2362_, v_a_2387_, v_oldTrace_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v___x_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2411_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_a_2393_ = lean_ctor_get(v___x_2391_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v_a_2399_; uint8_t v___x_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2397_ = lean_box(0);
v___x_2403_ = 0;
v___x_2404_ = lean_unbox(v_a_2392_);
lean_dec(v_a_2392_);
v___x_2405_ = l_Lake_instDecidableEqOutputStatus(v___x_2404_, v___x_2403_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_build_2364_);
lean_dec_ref(v_traceFile_2363_);
v_a_2399_ = v_a_2393_;
goto v___jp_2398_;
}
else
{
lean_object* v___f_2406_; lean_object* v___x_2407_; 
v___f_2406_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2407_ = l_Lake_buildAction___redArg(v___f_2406_, v_depTrace_2362_, v_traceFile_2363_, v_build_2364_, v_action_2365_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2393_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 1);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 2);
v_a_2399_ = v_a_2408_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2409_; lean_object* v_a_2410_; 
lean_del_object(v___x_2395_);
v_a_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2409_);
v_a_2410_ = lean_ctor_get(v___x_2407_, 1);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2407_, 2);
v_a_2375_ = v_a_2409_;
v_a_2376_ = v_a_2410_;
goto v___jp_2374_;
}
}
v___jp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v_a_2399_);
lean_ctor_set(v___x_2395_, 0, v___x_2397_);
v___x_2401_ = v___x_2395_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_a_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v_a_2413_; 
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_build_2364_);
lean_dec_ref(v_traceFile_2363_);
v_a_2412_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2412_);
v_a_2413_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2391_, 2);
v_a_2375_ = v_a_2412_;
v_a_2376_ = v_a_2413_;
goto v___jp_2374_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v_a_2416_; lean_object* v___x_2418_; 
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_build_2364_);
lean_dec_ref(v_traceFile_2363_);
lean_dec(v_info_2361_);
lean_dec_ref(v_inst_2360_);
lean_dec_ref(v_inst_2359_);
v_a_2415_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2415_);
v_a_2416_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2386_, 2);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_a_2416_);
v___x_2418_ = v___x_2384_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2416_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_trace_2381_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_buildTime_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3, v_action_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3 + 1, v_wantsRebuild_2380_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
v_a_2375_ = v_a_2415_;
v_a_2376_ = v___x_2418_;
goto v___jp_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_info_2423_, lean_object* v_depTrace_2424_, lean_object* v_traceFile_2425_, lean_object* v_build_2426_, lean_object* v_action_2427_, lean_object* v_oldTrace_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
uint8_t v_action_boxed_2436_; lean_object* v_res_2437_; 
v_action_boxed_2436_ = lean_unbox(v_action_2427_);
v_res_2437_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2421_, v_inst_2422_, v_info_2423_, v_depTrace_2424_, v_traceFile_2425_, v_build_2426_, v_action_boxed_2436_, v_oldTrace_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_oldTrace_2428_);
lean_dec_ref(v_depTrace_2424_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_info_2441_, lean_object* v_depTrace_2442_, lean_object* v_traceFile_2443_, lean_object* v_build_2444_, uint8_t v_action_2445_, lean_object* v_oldTrace_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_a_2455_; lean_object* v_a_2456_; lean_object* v_log_2458_; uint8_t v_action_2459_; uint8_t v_wantsRebuild_2460_; lean_object* v_trace_2461_; lean_object* v_buildTime_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2500_; 
v_log_2458_ = lean_ctor_get(v_a_2452_, 0);
v_action_2459_ = lean_ctor_get_uint8(v_a_2452_, sizeof(void*)*3);
v_wantsRebuild_2460_ = lean_ctor_get_uint8(v_a_2452_, sizeof(void*)*3 + 1);
v_trace_2461_ = lean_ctor_get(v_a_2452_, 1);
v_buildTime_2462_ = lean_ctor_get(v_a_2452_, 2);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_a_2452_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2464_ = v_a_2452_;
v_isShared_2465_ = v_isSharedCheck_2500_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_buildTime_2462_);
lean_inc(v_trace_2461_);
lean_inc(v_log_2458_);
lean_dec(v_a_2452_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2500_;
goto v_resetjp_2463_;
}
v___jp_2454_:
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_a_2455_);
lean_ctor_set(v___x_2457_, 1, v_a_2456_);
return v___x_2457_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; 
lean_inc_ref(v_traceFile_2443_);
v___x_2466_ = l_Lake_readTraceFile(v_traceFile_2443_, v_log_2458_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v_a_2468_; lean_object* v___x_2470_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
v_a_2468_ = lean_ctor_get(v___x_2466_, 1);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2466_, 2);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_a_2468_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2468_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_trace_2461_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_buildTime_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2494_, sizeof(void*)*3, v_action_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2494_, sizeof(void*)*3 + 1, v_wantsRebuild_2460_);
v___x_2470_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2439_, v_inst_2440_, v_info_2441_, v_depTrace_2442_, v_a_2467_, v_oldTrace_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v___x_2470_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2491_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_a_2473_ = lean_ctor_get(v___x_2471_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2475_ = v___x_2471_;
v_isShared_2476_ = v_isSharedCheck_2491_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2491_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v_a_2479_; uint8_t v___x_2483_; uint8_t v___x_2484_; uint8_t v___x_2485_; 
v___x_2477_ = lean_box(0);
v___x_2483_ = 0;
v___x_2484_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
v___x_2485_ = l_Lake_instDecidableEqOutputStatus(v___x_2484_, v___x_2483_);
if (v___x_2485_ == 0)
{
lean_dec_ref(v_a_2447_);
lean_dec_ref(v_build_2444_);
lean_dec_ref(v_traceFile_2443_);
v_a_2479_ = v_a_2473_;
goto v___jp_2478_;
}
else
{
lean_object* v___f_2486_; lean_object* v___x_2487_; 
v___f_2486_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2487_ = l_Lake_buildAction___redArg(v___f_2486_, v_depTrace_2442_, v_traceFile_2443_, v_build_2444_, v_action_2445_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2473_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 1);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 2);
v_a_2479_ = v_a_2488_;
goto v___jp_2478_;
}
else
{
lean_object* v_a_2489_; lean_object* v_a_2490_; 
lean_del_object(v___x_2475_);
v_a_2489_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2489_);
v_a_2490_ = lean_ctor_get(v___x_2487_, 1);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2487_, 2);
v_a_2455_ = v_a_2489_;
v_a_2456_ = v_a_2490_;
goto v___jp_2454_;
}
}
v___jp_2478_:
{
lean_object* v___x_2481_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v_a_2479_);
lean_ctor_set(v___x_2475_, 0, v___x_2477_);
v___x_2481_ = v___x_2475_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_a_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v_a_2493_; 
lean_dec_ref(v_a_2447_);
lean_dec_ref(v_build_2444_);
lean_dec_ref(v_traceFile_2443_);
v_a_2492_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2492_);
v_a_2493_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2471_, 2);
v_a_2455_ = v_a_2492_;
v_a_2456_ = v_a_2493_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; 
lean_dec_ref(v_a_2447_);
lean_dec_ref(v_build_2444_);
lean_dec_ref(v_traceFile_2443_);
lean_dec(v_info_2441_);
lean_dec_ref(v_inst_2440_);
lean_dec_ref(v_inst_2439_);
v_a_2495_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2495_);
v_a_2496_ = lean_ctor_get(v___x_2466_, 1);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2466_, 2);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_a_2496_);
v___x_2498_ = v___x_2464_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2496_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_trace_2461_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_buildTime_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3, v_action_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3 + 1, v_wantsRebuild_2460_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
v_a_2455_ = v_a_2495_;
v_a_2456_ = v___x_2498_;
goto v___jp_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_info_2504_, lean_object* v_depTrace_2505_, lean_object* v_traceFile_2506_, lean_object* v_build_2507_, lean_object* v_action_2508_, lean_object* v_oldTrace_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
uint8_t v_action_boxed_2517_; lean_object* v_res_2518_; 
v_action_boxed_2517_ = lean_unbox(v_action_2508_);
v_res_2518_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2501_, v_inst_2502_, v_inst_2503_, v_info_2504_, v_depTrace_2505_, v_traceFile_2506_, v_build_2507_, v_action_boxed_2517_, v_oldTrace_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_oldTrace_2509_);
lean_dec_ref(v_depTrace_2505_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2520_, uint64_t v_hash_2521_){
_start:
{
lean_object* v___x_2523_; lean_object* v_hashFile_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2524_ = lean_string_append(v_file_2520_, v___x_2523_);
lean_inc_ref(v_hashFile_2524_);
v___x_2525_ = l_Lake_createParentDirs(v_hashFile_2524_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec_ref_known(v___x_2525_, 1);
v___x_2526_ = l_Lake_lowerHexUInt64(v_hash_2521_);
v___x_2527_ = l_IO_FS_writeFile(v_hashFile_2524_, v___x_2526_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v_hashFile_2524_);
return v___x_2527_;
}
else
{
lean_dec_ref(v_hashFile_2524_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2528_, lean_object* v_hash_2529_, lean_object* v_a_2530_){
_start:
{
uint64_t v_hash_boxed_2531_; lean_object* v_res_2532_; 
v_hash_boxed_2531_ = lean_unbox_uint64(v_hash_2529_);
lean_dec_ref(v_hash_2529_);
v_res_2532_ = l_Lake_writeFileHash(v_file_2528_, v_hash_boxed_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2533_, uint8_t v_text_2534_){
_start:
{
lean_object* v___y_2537_; 
if (v_text_2534_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lake_computeBinFileHash(v_file_2533_);
v___y_2537_ = v___x_2549_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lake_computeTextFileHash(v_file_2533_);
v___y_2537_ = v___x_2550_;
goto v___jp_2536_;
}
v___jp_2536_:
{
if (lean_obj_tag(v___y_2537_) == 0)
{
lean_object* v_a_2538_; uint64_t v___x_2539_; lean_object* v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___y_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___y_2537_, 1);
v___x_2539_ = lean_unbox_uint64(v_a_2538_);
lean_dec(v_a_2538_);
v___x_2540_ = l_Lake_writeFileHash(v_file_2533_, v___x_2539_);
return v___x_2540_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_file_2533_);
v_a_2541_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___y_2537_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___y_2537_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2551_, lean_object* v_text_2552_, lean_object* v_a_2553_){
_start:
{
uint8_t v_text_boxed_2554_; lean_object* v_res_2555_; 
v_text_boxed_2554_ = lean_unbox(v_text_2552_);
v_res_2555_ = l_Lake_cacheFileHash(v_file_2551_, v_text_boxed_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2559_ = lean_string_append(v_file_2556_, v___x_2558_);
v___x_2560_ = l_Lake_removeFileIfExists(v___x_2559_);
lean_dec_ref(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lake_clearFileHash(v_file_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2564_, uint8_t v_text_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_toBuildConfig_2569_; uint8_t v_trustHash_2570_; lean_object* v___x_2571_; lean_object* v_hashFile_2572_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; uint8_t v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2612_; 
v_toBuildConfig_2569_ = lean_ctor_get(v_a_2566_, 0);
v_trustHash_2570_ = lean_ctor_get_uint8(v_toBuildConfig_2569_, sizeof(void*)*4 + 1);
v___x_2571_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2564_);
v_hashFile_2572_ = lean_string_append(v_file_2564_, v___x_2571_);
if (v_trustHash_2570_ == 0)
{
v___y_2612_ = v_a_2567_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lake_Hash_load_x3f(v_hashFile_2572_);
if (lean_obj_tag(v___x_2625_) == 1)
{
lean_object* v_val_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_hashFile_2572_);
lean_dec_ref(v_file_2564_);
v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_val_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_val_2626_);
lean_ctor_set(v___x_2627_, 1, v_a_2567_);
return v___x_2627_;
}
else
{
lean_dec(v___x_2625_);
v___y_2612_ = v_a_2567_;
goto v___jp_2611_;
}
}
v___jp_2573_:
{
if (lean_obj_tag(v___y_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; 
v_a_2580_ = lean_ctor_get(v___y_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___y_2579_, 1);
lean_inc_ref(v_hashFile_2572_);
v___x_2581_ = l_Lake_createParentDirs(v_hashFile_2572_);
if (lean_obj_tag(v___x_2581_) == 0)
{
uint64_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref_known(v___x_2581_, 1);
v___x_2582_ = lean_unbox_uint64(v_a_2580_);
v___x_2583_ = l_Lake_lowerHexUInt64(v___x_2582_);
v___x_2584_ = l_IO_FS_writeFile(v_hashFile_2572_, v___x_2583_);
lean_dec_ref(v___x_2583_);
lean_dec_ref(v_hashFile_2572_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2585_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2585_, 0, v___y_2575_);
lean_ctor_set(v___x_2585_, 1, v___y_2574_);
lean_ctor_set(v___x_2585_, 2, v___y_2578_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3, v___y_2577_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3 + 1, v___y_2576_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2580_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
return v___x_2586_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_a_2580_);
v_a_2587_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2588_ = lean_io_error_to_string(v_a_2587_);
v___x_2589_ = 3;
v___x_2590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*1, v___x_2589_);
v___x_2591_ = lean_array_get_size(v___y_2575_);
v___x_2592_ = lean_array_push(v___y_2575_, v___x_2590_);
v___x_2593_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___y_2574_);
lean_ctor_set(v___x_2593_, 2, v___y_2578_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3, v___y_2577_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3 + 1, v___y_2576_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
return v___x_2594_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec(v_a_2580_);
lean_dec_ref(v_hashFile_2572_);
v_a_2595_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2596_ = lean_io_error_to_string(v_a_2595_);
v___x_2597_ = 3;
v___x_2598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*1, v___x_2597_);
v___x_2599_ = lean_array_get_size(v___y_2575_);
v___x_2600_ = lean_array_push(v___y_2575_, v___x_2598_);
v___x_2601_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___y_2574_);
lean_ctor_set(v___x_2601_, 2, v___y_2578_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3, v___y_2577_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 1, v___y_2576_);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
return v___x_2602_;
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_hashFile_2572_);
v_a_2603_ = lean_ctor_get(v___y_2579_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___y_2579_, 1);
v___x_2604_ = lean_io_error_to_string(v_a_2603_);
v___x_2605_ = 3;
v___x_2606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*1, v___x_2605_);
v___x_2607_ = lean_array_get_size(v___y_2575_);
v___x_2608_ = lean_array_push(v___y_2575_, v___x_2606_);
v___x_2609_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___y_2574_);
lean_ctor_set(v___x_2609_, 2, v___y_2578_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*3, v___y_2577_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*3 + 1, v___y_2576_);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2607_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
return v___x_2610_;
}
}
v___jp_2611_:
{
if (v_text_2565_ == 0)
{
lean_object* v_log_2613_; uint8_t v_action_2614_; uint8_t v_wantsRebuild_2615_; lean_object* v_trace_2616_; lean_object* v_buildTime_2617_; lean_object* v___x_2618_; 
v_log_2613_ = lean_ctor_get(v___y_2612_, 0);
lean_inc_ref(v_log_2613_);
v_action_2614_ = lean_ctor_get_uint8(v___y_2612_, sizeof(void*)*3);
v_wantsRebuild_2615_ = lean_ctor_get_uint8(v___y_2612_, sizeof(void*)*3 + 1);
v_trace_2616_ = lean_ctor_get(v___y_2612_, 1);
lean_inc_ref(v_trace_2616_);
v_buildTime_2617_ = lean_ctor_get(v___y_2612_, 2);
lean_inc(v_buildTime_2617_);
lean_dec_ref(v___y_2612_);
v___x_2618_ = l_Lake_computeBinFileHash(v_file_2564_);
lean_dec_ref(v_file_2564_);
v___y_2574_ = v_trace_2616_;
v___y_2575_ = v_log_2613_;
v___y_2576_ = v_wantsRebuild_2615_;
v___y_2577_ = v_action_2614_;
v___y_2578_ = v_buildTime_2617_;
v___y_2579_ = v___x_2618_;
goto v___jp_2573_;
}
else
{
lean_object* v_log_2619_; uint8_t v_action_2620_; uint8_t v_wantsRebuild_2621_; lean_object* v_trace_2622_; lean_object* v_buildTime_2623_; lean_object* v___x_2624_; 
v_log_2619_ = lean_ctor_get(v___y_2612_, 0);
lean_inc_ref(v_log_2619_);
v_action_2620_ = lean_ctor_get_uint8(v___y_2612_, sizeof(void*)*3);
v_wantsRebuild_2621_ = lean_ctor_get_uint8(v___y_2612_, sizeof(void*)*3 + 1);
v_trace_2622_ = lean_ctor_get(v___y_2612_, 1);
lean_inc_ref(v_trace_2622_);
v_buildTime_2623_ = lean_ctor_get(v___y_2612_, 2);
lean_inc(v_buildTime_2623_);
lean_dec_ref(v___y_2612_);
v___x_2624_ = l_Lake_computeTextFileHash(v_file_2564_);
lean_dec_ref(v_file_2564_);
v___y_2574_ = v_trace_2622_;
v___y_2575_ = v_log_2619_;
v___y_2576_ = v_wantsRebuild_2621_;
v___y_2577_ = v_action_2620_;
v___y_2578_ = v_buildTime_2623_;
v___y_2579_ = v___x_2624_;
goto v___jp_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2628_, lean_object* v_text_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
uint8_t v_text_boxed_2633_; lean_object* v_res_2634_; 
v_text_boxed_2633_ = lean_unbox(v_text_2629_);
v_res_2634_ = l_Lake_fetchFileHash___redArg(v_file_2628_, v_text_boxed_2633_, v_a_2630_, v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2635_, uint8_t v_text_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lake_fetchFileHash___redArg(v_file_2635_, v_text_2636_, v_a_2641_, v_a_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2645_, lean_object* v_text_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
uint8_t v_text_boxed_2654_; lean_object* v_res_2655_; 
v_text_boxed_2654_ = lean_unbox(v_text_2646_);
v_res_2655_ = l_Lake_fetchFileHash(v_file_2645_, v_text_boxed_2654_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2656_, uint8_t v_text_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
lean_inc_ref(v_file_2656_);
v___x_2661_ = l_Lake_fetchFileHash___redArg(v_file_2656_, v_text_2657_, v_a_2658_, v_a_2659_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2700_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 1);
v_a_2663_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2665_ = v___x_2661_;
v_isShared_2666_ = v_isSharedCheck_2700_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2662_);
lean_inc(v_a_2663_);
lean_dec(v___x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2700_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_log_2667_; uint8_t v_action_2668_; uint8_t v_wantsRebuild_2669_; lean_object* v_trace_2670_; lean_object* v_buildTime_2671_; lean_object* v___x_2672_; 
v_log_2667_ = lean_ctor_get(v_a_2662_, 0);
v_action_2668_ = lean_ctor_get_uint8(v_a_2662_, sizeof(void*)*3);
v_wantsRebuild_2669_ = lean_ctor_get_uint8(v_a_2662_, sizeof(void*)*3 + 1);
v_trace_2670_ = lean_ctor_get(v_a_2662_, 1);
v_buildTime_2671_ = lean_ctor_get(v_a_2662_, 2);
v___x_2672_ = lean_io_metadata(v_file_2656_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v_modified_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint64_t v___x_2677_; lean_object* v___x_2679_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v_modified_2674_ = lean_ctor_get(v_a_2673_, 1);
lean_inc_ref(v_modified_2674_);
lean_dec(v_a_2673_);
v___x_2675_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2676_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2676_, 0, v_file_2656_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_ctor_set(v___x_2676_, 2, v_modified_2674_);
v___x_2677_ = lean_unbox_uint64(v_a_2663_);
lean_dec(v_a_2663_);
lean_ctor_set_uint64(v___x_2676_, sizeof(void*)*3, v___x_2677_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2676_);
v___x_2679_ = v___x_2665_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2662_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
else
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2696_; 
lean_inc(v_buildTime_2671_);
lean_inc_ref(v_trace_2670_);
lean_inc_ref(v_log_2667_);
lean_dec(v_a_2663_);
lean_dec_ref(v_file_2656_);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2662_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2697_ = lean_ctor_get(v_a_2662_, 2);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_a_2662_, 1);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_a_2662_, 0);
lean_dec(v_unused_2699_);
v___x_2682_ = v_a_2662_;
v_isShared_2683_ = v_isSharedCheck_2696_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v_a_2662_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2696_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_a_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v_a_2684_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2685_ = lean_io_error_to_string(v_a_2684_);
v___x_2686_ = 3;
v___x_2687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set_uint8(v___x_2687_, sizeof(void*)*1, v___x_2686_);
v___x_2688_ = lean_array_get_size(v_log_2667_);
v___x_2689_ = lean_array_push(v_log_2667_, v___x_2687_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2689_);
v___x_2691_ = v___x_2682_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_trace_2670_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_buildTime_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2695_, sizeof(void*)*3, v_action_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2695_, sizeof(void*)*3 + 1, v_wantsRebuild_2669_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 1);
lean_ctor_set(v___x_2665_, 1, v___x_2691_);
lean_ctor_set(v___x_2665_, 0, v___x_2688_);
v___x_2693_ = v___x_2665_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_file_2656_);
v_a_2701_ = lean_ctor_get(v___x_2661_, 0);
v_a_2702_ = lean_ctor_get(v___x_2661_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2661_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_inc(v_a_2701_);
lean_dec(v___x_2661_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2701_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2710_, lean_object* v_text_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_text_boxed_2715_; lean_object* v_res_2716_; 
v_text_boxed_2715_ = lean_unbox(v_text_2711_);
v_res_2716_ = l_Lake_fetchFileTrace___redArg(v_file_2710_, v_text_boxed_2715_, v_a_2712_, v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2717_, uint8_t v_text_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lake_fetchFileTrace___redArg(v_file_2717_, v_text_2718_, v_a_2723_, v_a_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2727_, lean_object* v_text_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_text_boxed_2736_; lean_object* v_res_2737_; 
v_text_boxed_2736_ = lean_unbox(v_text_2728_);
v_res_2737_ = l_Lake_fetchFileTrace(v_file_2727_, v_text_boxed_2736_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2738_, lean_object* v_a_x3f_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v_log_2743_; uint8_t v_action_2744_; uint8_t v_wantsRebuild_2745_; lean_object* v_trace_2746_; lean_object* v_buildTime_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2758_; 
v___x_2742_ = lean_io_mono_ms_now();
v_log_2743_ = lean_ctor_get(v___y_2740_, 0);
v_action_2744_ = lean_ctor_get_uint8(v___y_2740_, sizeof(void*)*3);
v_wantsRebuild_2745_ = lean_ctor_get_uint8(v___y_2740_, sizeof(void*)*3 + 1);
v_trace_2746_ = lean_ctor_get(v___y_2740_, 1);
v_buildTime_2747_ = lean_ctor_get(v___y_2740_, 2);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___y_2740_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2749_ = v___y_2740_;
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_buildTime_2747_);
lean_inc(v_trace_2746_);
lean_inc(v_log_2743_);
lean_dec(v___y_2740_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2751_ = lean_nat_sub(v___x_2742_, v_val_2738_);
lean_dec(v___x_2742_);
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_nat_add(v_buildTime_2747_, v___x_2751_);
lean_dec(v___x_2751_);
lean_dec(v_buildTime_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 2, v___x_2753_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_log_2743_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_trace_2746_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v___x_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*3, v_action_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*3 + 1, v_wantsRebuild_2745_);
v___x_2755_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2752_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2759_, lean_object* v_a_x3f_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2759_, v_a_x3f_2760_, v___y_2761_);
lean_dec(v_a_x3f_2760_);
lean_dec(v_val_2759_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2764_, lean_object* v_file_2765_, lean_object* v_a_2766_, lean_object* v_depTrace_2767_, lean_object* v_traceFile_2768_, uint8_t v_action_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_a_2777_; lean_object* v_a_2778_; lean_object* v_log_2781_; uint8_t v_action_2782_; uint8_t v_wantsRebuild_2783_; lean_object* v_trace_2784_; lean_object* v_buildTime_2785_; lean_object* v_toBuildConfig_2791_; lean_object* v_log_2792_; uint8_t v_action_2793_; uint8_t v_wantsRebuild_2794_; lean_object* v_trace_2795_; lean_object* v_buildTime_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2919_; 
v_toBuildConfig_2791_ = lean_ctor_get(v_a_2773_, 0);
v_log_2792_ = lean_ctor_get(v_a_2774_, 0);
v_action_2793_ = lean_ctor_get_uint8(v_a_2774_, sizeof(void*)*3);
v_wantsRebuild_2794_ = lean_ctor_get_uint8(v_a_2774_, sizeof(void*)*3 + 1);
v_trace_2795_ = lean_ctor_get(v_a_2774_, 1);
v_buildTime_2796_ = lean_ctor_get(v_a_2774_, 2);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2774_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2798_ = v_a_2774_;
v_isShared_2799_ = v_isSharedCheck_2919_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_buildTime_2796_);
lean_inc(v_trace_2795_);
lean_inc(v_log_2792_);
lean_dec(v_a_2774_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2919_;
goto v_resetjp_2797_;
}
v___jp_2776_:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2777_);
lean_ctor_set(v___x_2779_, 1, v_a_2778_);
return v___x_2779_;
}
v___jp_2780_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2786_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2787_ = lean_array_get_size(v_log_2781_);
v___x_2788_ = lean_array_push(v_log_2781_, v___x_2786_);
v___x_2789_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v_trace_2784_);
lean_ctor_set(v___x_2789_, 2, v_buildTime_2785_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*3, v_action_2782_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*3 + 1, v_wantsRebuild_2783_);
v___x_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2787_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
return v___x_2790_;
}
v_resetjp_2797_:
{
uint8_t v_noBuild_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_noBuild_2800_ = lean_ctor_get_uint8(v_toBuildConfig_2791_, sizeof(void*)*4 + 2);
v___x_2801_ = l_Lake_JobAction_merge(v_action_2793_, v_action_2769_);
v___x_2802_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2768_);
v___x_2803_ = l_System_FilePath_addExtension(v_traceFile_2768_, v___x_2802_);
if (v_noBuild_2800_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2792_);
if (v_isShared_2799_ == 0)
{
v___x_2806_ = v___x_2798_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_log_2792_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_trace_2795_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_buildTime_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*3 + 1, v_wantsRebuild_2794_);
v___x_2806_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v_a_2809_; lean_object* v_a_2810_; 
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*3, v___x_2801_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
v___x_2807_ = lean_apply_7(v_build_2764_, v_a_2766_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v___x_2806_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2814_; lean_object* v_log_2815_; uint8_t v_action_2816_; uint8_t v_wantsRebuild_2817_; lean_object* v_trace_2818_; lean_object* v_buildTime_2819_; lean_object* v___x_2820_; 
v_a_2814_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2807_, 2);
v_log_2815_ = lean_ctor_get(v_a_2814_, 0);
v_action_2816_ = lean_ctor_get_uint8(v_a_2814_, sizeof(void*)*3);
v_wantsRebuild_2817_ = lean_ctor_get_uint8(v_a_2814_, sizeof(void*)*3 + 1);
v_trace_2818_ = lean_ctor_get(v_a_2814_, 1);
v_buildTime_2819_ = lean_ctor_get(v_a_2814_, 2);
v___x_2820_ = l_Lake_clearFileHash(v_file_2765_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_array_get_size(v_log_2792_);
lean_dec_ref(v_log_2792_);
v___x_2823_ = lean_array_get_size(v_log_2815_);
v___x_2824_ = l_Array_extract___redArg(v_log_2815_, v___x_2822_, v___x_2823_);
v___x_2825_ = lean_box(0);
v___x_2826_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2767_, v___x_2825_, v___x_2824_);
v___x_2827_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2768_, v___x_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2868_; 
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2869_);
v___x_2829_ = v___x_2827_;
v_isShared_2830_ = v_isSharedCheck_2868_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v___x_2827_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2868_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lake_removeFileIfExists(v___x_2803_);
lean_dec_ref(v___x_2803_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2851_; 
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2852_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2851_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2851_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
lean_inc(v_a_2821_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v_a_2821_);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2821_);
v___x_2836_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 1);
lean_ctor_set(v___x_2829_, 0, v___x_2836_);
v___x_2838_ = v___x_2829_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v___x_2839_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2804_, v___x_2838_, v_a_2814_);
lean_dec_ref(v___x_2838_);
lean_dec(v___x_2804_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2839_, 0);
lean_dec(v_unused_2848_);
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_a_2821_);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2821_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
else
{
lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2864_; 
lean_inc(v_buildTime_2819_);
lean_inc_ref(v_trace_2818_);
lean_inc_ref(v_log_2815_);
lean_del_object(v___x_2829_);
lean_dec(v_a_2821_);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2814_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; lean_object* v_unused_2866_; lean_object* v_unused_2867_; 
v_unused_2865_ = lean_ctor_get(v_a_2814_, 2);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_a_2814_, 1);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_a_2814_, 0);
lean_dec(v_unused_2867_);
v___x_2854_ = v_a_2814_;
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
else
{
lean_dec(v_a_2814_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v_a_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v_a_2856_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2857_ = lean_io_error_to_string(v_a_2856_);
v___x_2858_ = 3;
v___x_2859_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2859_, 0, v___x_2857_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*1, v___x_2858_);
v___x_2860_ = lean_array_push(v_log_2815_, v___x_2859_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2860_);
v___x_2862_ = v___x_2854_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_trace_2818_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_buildTime_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*3, v_action_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2863_, sizeof(void*)*3 + 1, v_wantsRebuild_2817_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v_a_2809_ = v___x_2823_;
v_a_2810_ = v___x_2862_;
goto v___jp_2808_;
}
}
}
}
}
else
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2881_; 
lean_inc(v_buildTime_2819_);
lean_inc_ref(v_trace_2818_);
lean_inc_ref(v_log_2815_);
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2803_);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2814_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; lean_object* v_unused_2883_; lean_object* v_unused_2884_; 
v_unused_2882_ = lean_ctor_get(v_a_2814_, 2);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_a_2814_, 1);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_a_2814_, 0);
lean_dec(v_unused_2884_);
v___x_2871_ = v_a_2814_;
v_isShared_2872_ = v_isSharedCheck_2881_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v_a_2814_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2881_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_a_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v_a_2873_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2874_ = lean_io_error_to_string(v_a_2873_);
v___x_2875_ = 3;
v___x_2876_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set_uint8(v___x_2876_, sizeof(void*)*1, v___x_2875_);
v___x_2877_ = lean_array_push(v_log_2815_, v___x_2876_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2877_);
v___x_2879_ = v___x_2871_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_trace_2818_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_buildTime_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*3, v_action_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*3 + 1, v_wantsRebuild_2817_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v_a_2809_ = v___x_2823_;
v_a_2810_ = v___x_2879_;
goto v___jp_2808_;
}
}
}
}
else
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2897_; 
lean_inc(v_buildTime_2819_);
lean_inc_ref(v_trace_2818_);
lean_inc_ref(v_log_2815_);
lean_dec_ref(v___x_2803_);
lean_dec_ref(v_log_2792_);
lean_dec_ref(v_traceFile_2768_);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_a_2814_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; lean_object* v_unused_2899_; lean_object* v_unused_2900_; 
v_unused_2898_ = lean_ctor_get(v_a_2814_, 2);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_a_2814_, 1);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_a_2814_, 0);
lean_dec(v_unused_2900_);
v___x_2886_ = v_a_2814_;
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v_a_2814_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_a_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2889_ = lean_io_error_to_string(v_a_2888_);
v___x_2890_ = 3;
v___x_2891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*1, v___x_2890_);
v___x_2892_ = lean_array_get_size(v_log_2815_);
v___x_2893_ = lean_array_push(v_log_2815_, v___x_2891_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2893_);
v___x_2895_ = v___x_2886_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_trace_2818_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_buildTime_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*3, v_action_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*3 + 1, v_wantsRebuild_2817_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
v_a_2809_ = v___x_2892_;
v_a_2810_ = v___x_2895_;
goto v___jp_2808_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v_a_2902_; 
lean_dec_ref(v___x_2803_);
lean_dec_ref(v_log_2792_);
lean_dec_ref(v_traceFile_2768_);
lean_dec_ref(v_file_2765_);
v_a_2901_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2901_);
v_a_2902_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2807_, 2);
v_a_2809_ = v_a_2901_;
v_a_2810_ = v_a_2902_;
goto v___jp_2808_;
}
v___jp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v_a_2813_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2804_, v___x_2811_, v_a_2810_);
lean_dec(v___x_2804_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v_a_2777_ = v_a_2809_;
v_a_2778_ = v_a_2813_;
goto v___jp_2776_;
}
}
}
else
{
uint8_t v___x_2904_; 
lean_dec_ref(v_a_2766_);
lean_dec_ref(v_file_2765_);
lean_dec_ref(v_build_2764_);
v___x_2904_ = l_System_FilePath_pathExists(v_traceFile_2768_);
lean_dec_ref(v_traceFile_2768_);
if (v___x_2904_ == 0)
{
lean_dec_ref(v___x_2803_);
lean_del_object(v___x_2798_);
v_log_2781_ = v_log_2792_;
v_action_2782_ = v___x_2801_;
v_wantsRebuild_2783_ = v_noBuild_2800_;
v_trace_2784_ = v_trace_2795_;
v_buildTime_2785_ = v_buildTime_2796_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2907_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2767_, v___x_2905_, v___x_2906_);
v___x_2908_ = l_Lake_BuildMetadata_writeFile(v___x_2803_, v___x_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref_known(v___x_2908_, 1);
lean_del_object(v___x_2798_);
v_log_2781_ = v_log_2792_;
v_action_2782_ = v___x_2801_;
v_wantsRebuild_2783_ = v_noBuild_2800_;
v_trace_2784_ = v_trace_2795_;
v_buildTime_2785_ = v_buildTime_2796_;
goto v___jp_2780_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v___x_2910_ = lean_io_error_to_string(v_a_2909_);
v___x_2911_ = 3;
v___x_2912_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*1, v___x_2911_);
v___x_2913_ = lean_array_get_size(v_log_2792_);
v___x_2914_ = lean_array_push(v_log_2792_, v___x_2912_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2914_);
v___x_2916_ = v___x_2798_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_trace_2795_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_buildTime_2796_);
v___x_2916_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*3, v___x_2801_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*3 + 1, v_noBuild_2800_);
v___x_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2913_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
return v___x_2917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2920_, lean_object* v_file_2921_, lean_object* v_a_2922_, lean_object* v_depTrace_2923_, lean_object* v_traceFile_2924_, lean_object* v_action_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
uint8_t v_action_boxed_2932_; lean_object* v_res_2933_; 
v_action_boxed_2932_ = lean_unbox(v_action_2925_);
v_res_2933_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2920_, v_file_2921_, v_a_2922_, v_depTrace_2923_, v_traceFile_2924_, v_action_boxed_2932_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_depTrace_2923_);
return v_res_2933_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2934_, lean_object* v_self_2935_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_io_metadata(v_info_2934_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v_modified_2939_; uint8_t v___x_2940_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v_modified_2939_ = lean_ctor_get(v_a_2938_, 1);
lean_inc_ref(v_modified_2939_);
lean_dec(v_a_2938_);
v___x_2940_ = l_IO_FS_instOrdSystemTime_ord(v_self_2935_, v_modified_2939_);
lean_dec_ref(v_modified_2939_);
if (v___x_2940_ == 0)
{
uint8_t v___x_2941_; 
v___x_2941_ = 1;
return v___x_2941_;
}
else
{
uint8_t v___x_2942_; 
v___x_2942_ = 0;
return v___x_2942_;
}
}
else
{
uint8_t v___x_2943_; 
lean_dec_ref_known(v___x_2937_, 1);
v___x_2943_ = 0;
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2944_, lean_object* v_self_2945_, lean_object* v_a_2946_){
_start:
{
uint8_t v_res_2947_; lean_object* v_r_2948_; 
v_res_2947_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2944_, v_self_2945_);
lean_dec_ref(v_self_2945_);
lean_dec_ref(v_info_2944_);
v_r_2948_ = lean_box(v_res_2947_);
return v_r_2948_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
if (lean_obj_tag(v_x_2949_) == 0)
{
if (lean_obj_tag(v_x_2950_) == 0)
{
uint8_t v___x_2951_; 
v___x_2951_ = 1;
return v___x_2951_;
}
else
{
uint8_t v___x_2952_; 
v___x_2952_ = 0;
return v___x_2952_;
}
}
else
{
if (lean_obj_tag(v_x_2950_) == 0)
{
uint8_t v___x_2953_; 
v___x_2953_ = 0;
return v___x_2953_;
}
else
{
lean_object* v_val_2954_; lean_object* v_val_2955_; uint64_t v___x_2956_; uint64_t v___x_2957_; uint8_t v___x_2958_; 
v_val_2954_ = lean_ctor_get(v_x_2949_, 0);
v_val_2955_ = lean_ctor_get(v_x_2950_, 0);
v___x_2956_ = lean_unbox_uint64(v_val_2954_);
v___x_2957_ = lean_unbox_uint64(v_val_2955_);
v___x_2958_ = lean_uint64_dec_eq(v___x_2956_, v___x_2957_);
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2959_, lean_object* v_x_2960_){
_start:
{
uint8_t v_res_2961_; lean_object* v_r_2962_; 
v_res_2961_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2959_, v_x_2960_);
lean_dec(v_x_2960_);
lean_dec(v_x_2959_);
v_r_2962_ = lean_box(v_res_2961_);
return v_r_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2963_, lean_object* v_depTrace_2964_, lean_object* v_depHash_2965_, lean_object* v_oldTrace_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
uint64_t v_hash_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_hash_2970_ = lean_ctor_get_uint64(v_depTrace_2964_, sizeof(void*)*3);
v___x_2971_ = lean_box_uint64(v_hash_2970_);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
v___x_2973_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2972_, v_depHash_2965_);
lean_dec_ref_known(v___x_2972_, 1);
if (v___x_2973_ == 0)
{
lean_object* v_toBuildConfig_2974_; uint8_t v_oldMode_2975_; 
v_toBuildConfig_2974_ = lean_ctor_get(v_a_2967_, 0);
v_oldMode_2975_ = lean_ctor_get_uint8(v_toBuildConfig_2974_, sizeof(void*)*4);
if (v_oldMode_2975_ == 0)
{
uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = 0;
v___x_2977_ = lean_box(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_a_2968_);
return v___x_2978_;
}
else
{
uint8_t v___x_2979_; 
v___x_2979_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2963_, v_oldTrace_2966_);
if (v___x_2979_ == 0)
{
uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = 0;
v___x_2981_ = lean_box(v___x_2980_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v_a_2968_);
return v___x_2982_;
}
else
{
uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = 1;
v___x_2984_ = lean_box(v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v_a_2968_);
return v___x_2985_;
}
}
}
else
{
uint8_t v___x_2986_; 
v___x_2986_ = l_System_FilePath_pathExists(v_info_2963_);
if (v___x_2986_ == 0)
{
uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = 0;
v___x_2988_ = lean_box(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
lean_ctor_set(v___x_2989_, 1, v_a_2968_);
return v___x_2989_;
}
else
{
uint8_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = 2;
v___x_2991_ = lean_box(v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v_a_2968_);
return v___x_2992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2993_, lean_object* v_depTrace_2994_, lean_object* v_depHash_2995_, lean_object* v_oldTrace_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2993_, v_depTrace_2994_, v_depHash_2995_, v_oldTrace_2996_, v_a_2997_, v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec_ref(v_oldTrace_2996_);
lean_dec(v_depHash_2995_);
lean_dec_ref(v_depTrace_2994_);
lean_dec_ref(v_info_2993_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_3001_, lean_object* v_info_3002_, lean_object* v_depTrace_3003_, lean_object* v_savedTrace_3004_, lean_object* v_oldTrace_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
if (lean_obj_tag(v_savedTrace_3004_) == 2)
{
lean_object* v_data_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3062_; 
v_data_3012_ = lean_ctor_get(v_savedTrace_3004_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_savedTrace_3004_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3014_ = v_savedTrace_3004_;
v_isShared_3015_ = v_isSharedCheck_3062_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_data_3012_);
lean_dec(v_savedTrace_3004_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3062_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
uint64_t v_depHash_3016_; lean_object* v_log_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v_depHash_3016_ = lean_ctor_get_uint64(v_data_3012_, sizeof(void*)*3);
v_log_3017_ = lean_ctor_get(v_data_3012_, 2);
lean_inc_ref(v_log_3017_);
lean_dec_ref(v_data_3012_);
v___x_3018_ = lean_box_uint64(v_depHash_3016_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3018_);
v___x_3020_ = v___x_3014_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3060_; 
v___x_3021_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3002_, v_depTrace_3003_, v___x_3020_, v_oldTrace_3005_, v_a_3009_, v_a_3010_);
lean_dec_ref(v___x_3020_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_a_3023_ = lean_ctor_get(v___x_3021_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3025_ = v___x_3021_;
v_isShared_3026_ = v_isSharedCheck_3060_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3060_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___y_3028_; uint8_t v___x_3032_; uint8_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3032_ = 0;
v___x_3033_ = lean_unbox(v_a_3022_);
v___x_3034_ = l_Lake_instDecidableEqOutputStatus(v___x_3033_, v___x_3032_);
if (v___x_3034_ == 0)
{
lean_object* v_log_3035_; uint8_t v_action_3036_; uint8_t v_wantsRebuild_3037_; lean_object* v_trace_3038_; lean_object* v_buildTime_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3059_; 
v_log_3035_ = lean_ctor_get(v_a_3023_, 0);
v_action_3036_ = lean_ctor_get_uint8(v_a_3023_, sizeof(void*)*3);
v_wantsRebuild_3037_ = lean_ctor_get_uint8(v_a_3023_, sizeof(void*)*3 + 1);
v_trace_3038_ = lean_ctor_get(v_a_3023_, 1);
v_buildTime_3039_ = lean_ctor_get(v_a_3023_, 2);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_a_3023_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3041_ = v_a_3023_;
v_isShared_3042_ = v_isSharedCheck_3059_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_buildTime_3039_);
lean_inc(v_trace_3038_);
lean_inc(v_log_3035_);
lean_dec(v_a_3023_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3059_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
uint8_t v___x_3043_; uint8_t v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = 2;
v___x_3044_ = l_Lake_JobAction_merge(v_action_3036_, v___x_3043_);
if (v_isShared_3042_ == 0)
{
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_log_3035_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_trace_3038_);
lean_ctor_set(v_reuseFailAlloc_3058_, 2, v_buildTime_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3058_, sizeof(void*)*3 + 1, v_wantsRebuild_3037_);
v___x_3046_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; 
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*3, v___x_3044_);
v___x_3047_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3017_, v_a_3001_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v___x_3046_);
lean_dec_ref(v_log_3017_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 2);
v___y_3028_ = v_a_3048_;
goto v___jp_3027_;
}
else
{
lean_object* v_a_3049_; lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3022_);
v_a_3049_ = lean_ctor_get(v___x_3047_, 0);
v_a_3050_ = lean_ctor_get(v___x_3047_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3047_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_inc(v_a_3049_);
lean_dec(v___x_3047_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3049_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_3017_);
v___y_3028_ = v_a_3023_;
goto v___jp_3027_;
}
v___jp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 1, v___y_3028_);
v___x_3030_ = v___x_3025_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3022_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___y_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3063_; uint8_t v_oldMode_3064_; 
lean_dec(v_savedTrace_3004_);
v_toBuildConfig_3063_ = lean_ctor_get(v_a_3009_, 0);
v_oldMode_3064_ = lean_ctor_get_uint8(v_toBuildConfig_3063_, sizeof(void*)*4);
if (v_oldMode_3064_ == 0)
{
uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = 0;
v___x_3066_ = lean_box(v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v_a_3010_);
return v___x_3067_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_3002_, v_oldTrace_3005_);
if (v___x_3068_ == 0)
{
uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = 0;
v___x_3070_ = lean_box(v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v_a_3010_);
return v___x_3071_;
}
else
{
uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = 1;
v___x_3073_ = lean_box(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v_a_3010_);
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3075_, lean_object* v_info_3076_, lean_object* v_depTrace_3077_, lean_object* v_savedTrace_3078_, lean_object* v_oldTrace_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3075_, v_info_3076_, v_depTrace_3077_, v_savedTrace_3078_, v_oldTrace_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_oldTrace_3079_);
lean_dec_ref(v_depTrace_3077_);
lean_dec_ref(v_info_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3088_, lean_object* v_build_3089_, uint8_t v_text_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_a_3099_; lean_object* v_a_3100_; lean_object* v_a_3103_; lean_object* v_log_3136_; uint8_t v_action_3137_; uint8_t v_wantsRebuild_3138_; lean_object* v_trace_3139_; lean_object* v_buildTime_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3171_; 
v_log_3136_ = lean_ctor_get(v_a_3096_, 0);
v_action_3137_ = lean_ctor_get_uint8(v_a_3096_, sizeof(void*)*3);
v_wantsRebuild_3138_ = lean_ctor_get_uint8(v_a_3096_, sizeof(void*)*3 + 1);
v_trace_3139_ = lean_ctor_get(v_a_3096_, 1);
v_buildTime_3140_ = lean_ctor_get(v_a_3096_, 2);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_a_3096_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3142_ = v_a_3096_;
v_isShared_3143_ = v_isSharedCheck_3171_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_buildTime_3140_);
lean_inc(v_trace_3139_);
lean_inc(v_log_3136_);
lean_dec(v_a_3096_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3171_;
goto v_resetjp_3141_;
}
v___jp_3098_:
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3101_, 0, v_a_3099_);
lean_ctor_set(v___x_3101_, 1, v_a_3100_);
return v___x_3101_;
}
v___jp_3102_:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lake_fetchFileTrace___redArg(v_file_3088_, v_text_3090_, v_a_3095_, v_a_3103_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3126_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 1);
v_a_3106_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3108_ = v___x_3104_;
v_isShared_3109_ = v_isSharedCheck_3126_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3105_);
lean_inc(v_a_3106_);
lean_dec(v___x_3104_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3126_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_log_3110_; uint8_t v_action_3111_; uint8_t v_wantsRebuild_3112_; lean_object* v_buildTime_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3124_; 
v_log_3110_ = lean_ctor_get(v_a_3105_, 0);
v_action_3111_ = lean_ctor_get_uint8(v_a_3105_, sizeof(void*)*3);
v_wantsRebuild_3112_ = lean_ctor_get_uint8(v_a_3105_, sizeof(void*)*3 + 1);
v_buildTime_3113_ = lean_ctor_get(v_a_3105_, 2);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3105_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_3105_, 1);
lean_dec(v_unused_3125_);
v___x_3115_ = v_a_3105_;
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_buildTime_3113_);
lean_inc(v_log_3110_);
lean_dec(v_a_3105_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_box(0);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v_a_3106_);
v___x_3119_ = v___x_3115_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_log_3110_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_a_3106_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_buildTime_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*3, v_action_3111_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*3 + 1, v_wantsRebuild_3112_);
v___x_3119_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3121_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 1, v___x_3119_);
lean_ctor_set(v___x_3108_, 0, v___x_3117_);
v___x_3121_ = v___x_3108_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_a_3127_ = lean_ctor_get(v___x_3104_, 0);
v_a_3128_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3104_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_inc(v_a_3127_);
lean_dec(v___x_3104_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3127_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v_traceFile_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3088_);
v_traceFile_3145_ = lean_string_append(v_file_3088_, v___x_3144_);
lean_inc_ref(v_traceFile_3145_);
v___x_3146_ = l_Lake_readTraceFile(v_traceFile_3145_, v_log_3136_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_a_3148_; lean_object* v_mtime_3149_; lean_object* v___x_3151_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v_mtime_3149_ = lean_ctor_get(v_trace_3139_, 2);
lean_inc_ref(v_trace_3139_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_a_3148_);
v___x_3151_ = v___x_3142_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3148_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_trace_3139_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_buildTime_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3165_, sizeof(void*)*3, v_action_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3165_, sizeof(void*)*3 + 1, v_wantsRebuild_3138_);
v___x_3151_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3091_, v_file_3088_, v_trace_3139_, v_a_3147_, v_mtime_3149_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v___x_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v_a_3154_; uint8_t v___x_3155_; uint8_t v___x_3156_; uint8_t v___x_3157_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
v_a_3154_ = lean_ctor_get(v___x_3152_, 1);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3152_, 2);
v___x_3155_ = 0;
v___x_3156_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
v___x_3157_ = l_Lake_instDecidableEqOutputStatus(v___x_3156_, v___x_3155_);
if (v___x_3157_ == 0)
{
lean_dec_ref(v_traceFile_3145_);
lean_dec_ref(v_trace_3139_);
lean_dec_ref(v_a_3091_);
lean_dec_ref(v_build_3089_);
v_a_3103_ = v_a_3154_;
goto v___jp_3102_;
}
else
{
uint8_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = 5;
lean_inc_ref(v_file_3088_);
v___x_3159_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3089_, v_file_3088_, v_a_3091_, v_trace_3139_, v_traceFile_3145_, v___x_3158_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3154_);
lean_dec_ref(v_trace_3139_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 1);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 2);
v_a_3103_ = v_a_3160_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3161_; lean_object* v_a_3162_; 
lean_dec_ref(v_file_3088_);
v_a_3161_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3161_);
v_a_3162_ = lean_ctor_get(v___x_3159_, 1);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3159_, 2);
v_a_3099_ = v_a_3161_;
v_a_3100_ = v_a_3162_;
goto v___jp_3098_;
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v_a_3164_; 
lean_dec_ref(v_traceFile_3145_);
lean_dec_ref(v_trace_3139_);
lean_dec_ref(v_a_3091_);
lean_dec_ref(v_build_3089_);
lean_dec_ref(v_file_3088_);
v_a_3163_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3163_);
v_a_3164_ = lean_ctor_get(v___x_3152_, 1);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3152_, 2);
v_a_3099_ = v_a_3163_;
v_a_3100_ = v_a_3164_;
goto v___jp_3098_;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v_a_3167_; lean_object* v___x_3169_; 
lean_dec_ref(v_traceFile_3145_);
lean_dec_ref(v_a_3091_);
lean_dec_ref(v_build_3089_);
lean_dec_ref(v_file_3088_);
v_a_3166_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3166_);
v_a_3167_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3146_, 2);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_a_3167_);
v___x_3169_ = v___x_3142_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3167_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_trace_3139_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_buildTime_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3, v_action_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3 + 1, v_wantsRebuild_3138_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v_a_3099_ = v_a_3166_;
v_a_3100_ = v___x_3169_;
goto v___jp_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3172_, lean_object* v_build_3173_, lean_object* v_text_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
uint8_t v_text_boxed_3182_; lean_object* v_res_3183_; 
v_text_boxed_3182_ = lean_unbox(v_text_3174_);
v_res_3183_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3172_, v_build_3173_, v_text_boxed_3182_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec(v_a_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3184_, lean_object* v_info_3185_, lean_object* v_depTrace_3186_, lean_object* v_depHash_3187_, lean_object* v_oldTrace_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3185_, v_depTrace_3186_, v_depHash_3187_, v_oldTrace_3188_, v_a_3192_, v_a_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3196_, lean_object* v_info_3197_, lean_object* v_depTrace_3198_, lean_object* v_depHash_3199_, lean_object* v_oldTrace_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3196_, v_info_3197_, v_depTrace_3198_, v_depHash_3199_, v_oldTrace_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec_ref(v_oldTrace_3200_);
lean_dec(v_depHash_3199_);
lean_dec_ref(v_depTrace_3198_);
lean_dec_ref(v_info_3197_);
lean_dec_ref(v_a_3196_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v_file_3210_, uint64_t v___x_3211_, lean_object* v___x_3212_, uint8_t v_useLocalFile_3213_, lean_object* v_____r_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_IO_setAccessRights(v___x_3208_, v___x_3209_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3216_, 1);
lean_inc_ref(v_file_3210_);
v___x_3217_ = l_Lake_writeFileHash(v_file_3210_, v___x_3211_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref_known(v___x_3217_, 1);
v___x_3218_ = lean_io_metadata(v___x_3208_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3231_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3231_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3231_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_modified_3223_; lean_object* v___y_3225_; 
v_modified_3223_ = lean_ctor_get(v_a_3219_, 1);
lean_inc_ref(v_modified_3223_);
lean_dec(v_a_3219_);
if (v_useLocalFile_3213_ == 0)
{
v___y_3225_ = v___x_3208_;
goto v___jp_3224_;
}
else
{
lean_dec_ref(v___x_3208_);
lean_inc_ref(v_file_3210_);
v___y_3225_ = v_file_3210_;
goto v___jp_3224_;
}
v___jp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3212_);
lean_ctor_set(v___x_3226_, 1, v___y_3225_);
lean_ctor_set(v___x_3226_, 2, v_file_3210_);
lean_ctor_set(v___x_3226_, 3, v_modified_3223_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3227_);
v___x_3229_ = v___x_3221_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___x_3212_);
lean_dec_ref(v_file_3210_);
lean_dec_ref(v___x_3208_);
v_a_3232_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3218_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3218_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___x_3212_);
lean_dec_ref(v_file_3210_);
lean_dec_ref(v___x_3208_);
v_a_3240_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3217_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3217_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___x_3212_);
lean_dec_ref(v_file_3210_);
lean_dec_ref(v___x_3208_);
v_a_3248_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3216_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3216_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3256_, lean_object* v___x_3257_, lean_object* v_file_3258_, lean_object* v___x_3259_, lean_object* v___x_3260_, lean_object* v_useLocalFile_3261_, lean_object* v_____r_3262_, lean_object* v___y_3263_){
_start:
{
uint64_t v___x_2969__boxed_3264_; uint8_t v_useLocalFile_boxed_3265_; lean_object* v_res_3266_; 
v___x_2969__boxed_3264_ = lean_unbox_uint64(v___x_3259_);
lean_dec_ref(v___x_3259_);
v_useLocalFile_boxed_3265_ = lean_unbox(v_useLocalFile_3261_);
v_res_3266_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3256_, v___x_3257_, v_file_3258_, v___x_2969__boxed_3264_, v___x_3260_, v_useLocalFile_boxed_3265_, v_____r_3262_);
lean_dec_ref(v___x_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3274_, lean_object* v_file_3275_, lean_object* v_ext_3276_, uint8_t v_text_3277_, uint8_t v_exe_3278_, uint8_t v_useLocalFile_3279_){
_start:
{
lean_object* v_a_3282_; lean_object* v___y_3289_; uint8_t v___x_3300_; 
v___x_3300_ = 1;
if (v_text_3277_ == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = l_IO_FS_readBinFile(v_file_3275_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; uint64_t v___x_3303_; uint64_t v___x_3304_; uint64_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___y_3310_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = l_Lake_Hash_nil;
v___x_3304_ = lean_byte_array_hash(v_a_3302_);
v___x_3305_ = lean_uint64_mix_hash(v___x_3303_, v___x_3304_);
lean_inc_ref(v_ext_3276_);
v___x_3306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3306_, 0, v_ext_3276_);
lean_ctor_set_uint64(v___x_3306_, sizeof(void*)*1, v___x_3305_);
v___x_3307_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3308_ = l_System_FilePath_join(v_cache_3274_, v___x_3307_);
v___x_3331_ = lean_string_utf8_byte_size(v_ext_3276_);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_nat_dec_eq(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3334_ = l_Lake_lowerHexUInt64(v___x_3305_);
v___x_3335_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3336_ = lean_string_append(v___x_3334_, v___x_3335_);
v___x_3337_ = lean_string_append(v___x_3336_, v_ext_3276_);
lean_dec_ref(v_ext_3276_);
v___y_3310_ = v___x_3337_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3338_; 
lean_dec_ref(v_ext_3276_);
v___x_3338_ = l_Lake_lowerHexUInt64(v___x_3305_);
v___y_3310_ = v___x_3338_;
goto v___jp_3309_;
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3311_, 0, v___x_3300_);
lean_ctor_set_uint8(v___x_3311_, 1, v_text_3277_);
lean_ctor_set_uint8(v___x_3311_, 2, v_exe_3278_);
lean_inc_ref_n(v___x_3311_, 2);
v___x_3312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_ctor_set(v___x_3312_, 2, v___x_3311_);
v___x_3313_ = l_IO_setAccessRights(v_file_3275_, v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
lean_dec_ref_known(v___x_3313_, 1);
v___x_3314_ = l_Lake_joinRelative(v___x_3308_, v___y_3310_);
v___x_3315_ = l_System_FilePath_pathExists(v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_inc_ref(v___x_3314_);
v___x_3316_ = l_Lake_createParentDirs(v___x_3314_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; 
lean_dec_ref_known(v___x_3316_, 1);
v___x_3317_ = lean_io_hard_link(v_file_3275_, v___x_3314_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref_known(v___x_3317_, 1);
lean_dec(v_a_3302_);
v___x_3318_ = lean_box(0);
v___x_3319_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3314_, v___x_3312_, v_file_3275_, v___x_3305_, v___x_3306_, v_useLocalFile_3279_, v___x_3318_);
lean_dec_ref_known(v___x_3312_, 3);
v___y_3289_ = v___x_3319_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3317_, 1);
if (lean_obj_tag(v_a_3320_) == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec_ref_known(v_a_3320_, 2);
lean_dec(v_a_3302_);
v___x_3321_ = lean_box(0);
v___x_3322_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3314_, v___x_3312_, v_file_3275_, v___x_3305_, v___x_3306_, v_useLocalFile_3279_, v___x_3321_);
lean_dec_ref_known(v___x_3312_, 3);
v___y_3289_ = v___x_3322_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3323_; 
lean_dec(v_a_3320_);
v___x_3323_ = l_Lake_writeBinFileIfNew(v___x_3314_, v_a_3302_);
lean_dec(v_a_3302_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3314_, v___x_3312_, v_file_3275_, v___x_3305_, v___x_3306_, v_useLocalFile_3279_, v_a_3324_);
lean_dec_ref_known(v___x_3312_, 3);
v___y_3289_ = v___x_3325_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3326_; 
lean_dec_ref(v___x_3314_);
lean_dec_ref_known(v___x_3312_, 3);
lean_dec_ref_known(v___x_3306_, 1);
lean_dec_ref(v_file_3275_);
v_a_3326_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3323_, 1);
v_a_3282_ = v_a_3326_;
goto v___jp_3281_;
}
}
}
}
else
{
lean_object* v_a_3327_; 
lean_dec_ref(v___x_3314_);
lean_dec_ref_known(v___x_3312_, 3);
lean_dec_ref_known(v___x_3306_, 1);
lean_dec(v_a_3302_);
lean_dec_ref(v_file_3275_);
v_a_3327_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3316_, 1);
v_a_3282_ = v_a_3327_;
goto v___jp_3281_;
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v_a_3302_);
v___x_3328_ = lean_box(0);
v___x_3329_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3314_, v___x_3312_, v_file_3275_, v___x_3305_, v___x_3306_, v_useLocalFile_3279_, v___x_3328_);
lean_dec_ref_known(v___x_3312_, 3);
v___y_3289_ = v___x_3329_;
goto v___jp_3288_;
}
}
else
{
lean_object* v_a_3330_; 
lean_dec_ref_known(v___x_3312_, 3);
lean_dec_ref(v___y_3310_);
lean_dec_ref(v___x_3308_);
lean_dec_ref_known(v___x_3306_, 1);
lean_dec(v_a_3302_);
lean_dec_ref(v_file_3275_);
v_a_3330_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3313_, 1);
v_a_3282_ = v_a_3330_;
goto v___jp_3281_;
}
}
}
else
{
lean_object* v_a_3339_; 
lean_dec_ref(v_ext_3276_);
lean_dec_ref(v_file_3275_);
lean_dec_ref(v_cache_3274_);
v_a_3339_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3301_, 1);
v_a_3282_ = v_a_3339_;
goto v___jp_3281_;
}
}
else
{
lean_object* v___x_3340_; 
v___x_3340_ = l_IO_FS_readFile(v_file_3275_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; uint64_t v___x_3343_; uint64_t v___x_3344_; uint64_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___y_3350_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = l_String_crlfToLf(v_a_3341_);
lean_dec(v_a_3341_);
v___x_3343_ = l_Lake_Hash_nil;
v___x_3344_ = lean_string_hash(v___x_3342_);
v___x_3345_ = lean_uint64_mix_hash(v___x_3343_, v___x_3344_);
lean_inc_ref(v_ext_3276_);
v___x_3346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3346_, 0, v_ext_3276_);
lean_ctor_set_uint64(v___x_3346_, sizeof(void*)*1, v___x_3345_);
v___x_3347_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3348_ = l_System_FilePath_join(v_cache_3274_, v___x_3347_);
v___x_3364_ = lean_string_utf8_byte_size(v_ext_3276_);
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_nat_dec_eq(v___x_3364_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3367_ = l_Lake_lowerHexUInt64(v___x_3345_);
v___x_3368_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3369_ = lean_string_append(v___x_3367_, v___x_3368_);
v___x_3370_ = lean_string_append(v___x_3369_, v_ext_3276_);
lean_dec_ref(v_ext_3276_);
v___y_3350_ = v___x_3370_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3371_; 
lean_dec_ref(v_ext_3276_);
v___x_3371_ = l_Lake_lowerHexUInt64(v___x_3345_);
v___y_3350_ = v___x_3371_;
goto v___jp_3349_;
}
v___jp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3352_ = l_IO_setAccessRights(v_file_3275_, v___x_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3353_; uint8_t v___x_3354_; 
lean_dec_ref_known(v___x_3352_, 1);
v___x_3353_ = l_Lake_joinRelative(v___x_3348_, v___y_3350_);
v___x_3354_ = l_System_FilePath_pathExists(v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_inc_ref(v___x_3353_);
v___x_3355_ = l_Lake_createParentDirs(v___x_3353_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref_known(v___x_3355_, 1);
v___x_3356_ = l_Lake_writeFileIfNew(v___x_3353_, v___x_3342_);
lean_dec_ref(v___x_3342_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3353_, v___x_3351_, v_file_3275_, v___x_3345_, v___x_3346_, v_useLocalFile_3279_, v_a_3357_);
v___y_3289_ = v___x_3358_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3359_; 
lean_dec_ref(v___x_3353_);
lean_dec_ref_known(v___x_3346_, 1);
lean_dec_ref(v_file_3275_);
v_a_3359_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3356_, 1);
v_a_3282_ = v_a_3359_;
goto v___jp_3281_;
}
}
else
{
lean_object* v_a_3360_; 
lean_dec_ref(v___x_3353_);
lean_dec_ref_known(v___x_3346_, 1);
lean_dec_ref(v___x_3342_);
lean_dec_ref(v_file_3275_);
v_a_3360_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3355_, 1);
v_a_3282_ = v_a_3360_;
goto v___jp_3281_;
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_dec_ref(v___x_3342_);
v___x_3361_ = lean_box(0);
v___x_3362_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3353_, v___x_3351_, v_file_3275_, v___x_3345_, v___x_3346_, v_useLocalFile_3279_, v___x_3361_);
v___y_3289_ = v___x_3362_;
goto v___jp_3288_;
}
}
else
{
lean_object* v_a_3363_; 
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___x_3348_);
lean_dec_ref_known(v___x_3346_, 1);
lean_dec_ref(v___x_3342_);
lean_dec_ref(v_file_3275_);
v_a_3363_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3352_, 1);
v_a_3282_ = v_a_3363_;
goto v___jp_3281_;
}
}
}
else
{
lean_object* v_a_3372_; 
lean_dec_ref(v_ext_3276_);
lean_dec_ref(v_file_3275_);
lean_dec_ref(v_cache_3274_);
v_a_3372_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3340_, 1);
v_a_3282_ = v_a_3372_;
goto v___jp_3281_;
}
}
v___jp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3283_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3284_ = lean_io_error_to_string(v_a_3282_);
v___x_3285_ = lean_string_append(v___x_3283_, v___x_3284_);
lean_dec_ref(v___x_3284_);
v___x_3286_ = lean_mk_io_user_error(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
v___jp_3288_:
{
if (lean_obj_tag(v___y_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3298_; 
v_a_3290_ = lean_ctor_get(v___y_3289_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___y_3289_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3292_ = v___y_3289_;
v_isShared_3293_ = v_isSharedCheck_3298_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___y_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3298_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_a_3294_; lean_object* v___x_3296_; 
v_a_3294_ = lean_ctor_get(v_a_3290_, 0);
lean_inc(v_a_3294_);
lean_dec(v_a_3290_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_a_3294_);
v___x_3296_ = v___x_3292_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
else
{
lean_object* v_a_3299_; 
v_a_3299_ = lean_ctor_get(v___y_3289_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___y_3289_, 1);
v_a_3282_ = v_a_3299_;
goto v___jp_3281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3373_, lean_object* v_file_3374_, lean_object* v_ext_3375_, lean_object* v_text_3376_, lean_object* v_exe_3377_, lean_object* v_useLocalFile_3378_, lean_object* v_a_3379_){
_start:
{
uint8_t v_text_boxed_3380_; uint8_t v_exe_boxed_3381_; uint8_t v_useLocalFile_boxed_3382_; lean_object* v_res_3383_; 
v_text_boxed_3380_ = lean_unbox(v_text_3376_);
v_exe_boxed_3381_ = lean_unbox(v_exe_3377_);
v_useLocalFile_boxed_3382_ = lean_unbox(v_useLocalFile_3378_);
v_res_3383_ = l_Lake_Cache_saveArtifact(v_cache_3373_, v_file_3374_, v_ext_3375_, v_text_boxed_3380_, v_exe_boxed_3381_, v_useLocalFile_boxed_3382_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3384_){
_start:
{
lean_object* v_lakeCache_3385_; 
v_lakeCache_3385_ = lean_ctor_get(v_x_3384_, 2);
lean_inc_ref(v_lakeCache_3385_);
return v_lakeCache_3385_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3386_);
lean_dec_ref(v_x_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3388_, lean_object* v_ext_3389_, uint8_t v_text_3390_, uint8_t v_exe_3391_, uint8_t v_useLocalFile_3392_, lean_object* v_inst_3393_, lean_object* v_____do__lift_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3395_ = lean_box(v_text_3390_);
v___x_3396_ = lean_box(v_exe_3391_);
v___x_3397_ = lean_box(v_useLocalFile_3392_);
v___x_3398_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3398_, 0, v_____do__lift_3394_);
lean_closure_set(v___x_3398_, 1, v_file_3388_);
lean_closure_set(v___x_3398_, 2, v_ext_3389_);
lean_closure_set(v___x_3398_, 3, v___x_3395_);
lean_closure_set(v___x_3398_, 4, v___x_3396_);
lean_closure_set(v___x_3398_, 5, v___x_3397_);
v___x_3399_ = lean_apply_2(v_inst_3393_, lean_box(0), v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3400_, lean_object* v_ext_3401_, lean_object* v_text_3402_, lean_object* v_exe_3403_, lean_object* v_useLocalFile_3404_, lean_object* v_inst_3405_, lean_object* v_____do__lift_3406_){
_start:
{
uint8_t v_text_boxed_3407_; uint8_t v_exe_boxed_3408_; uint8_t v_useLocalFile_boxed_3409_; lean_object* v_res_3410_; 
v_text_boxed_3407_ = lean_unbox(v_text_3402_);
v_exe_boxed_3408_ = lean_unbox(v_exe_3403_);
v_useLocalFile_boxed_3409_ = lean_unbox(v_useLocalFile_3404_);
v_res_3410_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3400_, v_ext_3401_, v_text_boxed_3407_, v_exe_boxed_3408_, v_useLocalFile_boxed_3409_, v_inst_3405_, v_____do__lift_3406_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_file_3415_, lean_object* v_ext_3416_, uint8_t v_text_3417_, uint8_t v_exe_3418_, uint8_t v_useLocalFile_3419_){
_start:
{
lean_object* v_toApplicative_3420_; lean_object* v_toFunctor_3421_; lean_object* v_toBind_3422_; lean_object* v_map_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_toApplicative_3420_ = lean_ctor_get(v_inst_3414_, 0);
v_toFunctor_3421_ = lean_ctor_get(v_toApplicative_3420_, 0);
lean_inc_ref(v_toFunctor_3421_);
v_toBind_3422_ = lean_ctor_get(v_inst_3414_, 1);
lean_inc(v_toBind_3422_);
lean_dec_ref(v_inst_3414_);
v_map_3423_ = lean_ctor_get(v_toFunctor_3421_, 0);
lean_inc(v_map_3423_);
lean_dec_ref(v_toFunctor_3421_);
v___f_3424_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3425_ = lean_box(v_text_3417_);
v___x_3426_ = lean_box(v_exe_3418_);
v___x_3427_ = lean_box(v_useLocalFile_3419_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3428_, 0, v_file_3415_);
lean_closure_set(v___f_3428_, 1, v_ext_3416_);
lean_closure_set(v___f_3428_, 2, v___x_3425_);
lean_closure_set(v___f_3428_, 3, v___x_3426_);
lean_closure_set(v___f_3428_, 4, v___x_3427_);
lean_closure_set(v___f_3428_, 5, v_inst_3413_);
v___x_3429_ = lean_apply_4(v_map_3423_, lean_box(0), lean_box(0), v___f_3424_, v_inst_3412_);
v___x_3430_ = lean_apply_4(v_toBind_3422_, lean_box(0), lean_box(0), v___x_3429_, v___f_3428_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_file_3434_, lean_object* v_ext_3435_, lean_object* v_text_3436_, lean_object* v_exe_3437_, lean_object* v_useLocalFile_3438_){
_start:
{
uint8_t v_text_boxed_3439_; uint8_t v_exe_boxed_3440_; uint8_t v_useLocalFile_boxed_3441_; lean_object* v_res_3442_; 
v_text_boxed_3439_ = lean_unbox(v_text_3436_);
v_exe_boxed_3440_ = lean_unbox(v_exe_3437_);
v_useLocalFile_boxed_3441_ = lean_unbox(v_useLocalFile_3438_);
v_res_3442_ = l_Lake_cacheArtifact___redArg(v_inst_3431_, v_inst_3432_, v_inst_3433_, v_file_3434_, v_ext_3435_, v_text_boxed_3439_, v_exe_boxed_3440_, v_useLocalFile_boxed_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3443_, lean_object* v_inst_3444_, lean_object* v_inst_3445_, lean_object* v_inst_3446_, lean_object* v_file_3447_, lean_object* v_ext_3448_, uint8_t v_text_3449_, uint8_t v_exe_3450_, uint8_t v_useLocalFile_3451_){
_start:
{
lean_object* v_toApplicative_3452_; lean_object* v_toFunctor_3453_; lean_object* v_toBind_3454_; lean_object* v_map_3455_; lean_object* v___f_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_toApplicative_3452_ = lean_ctor_get(v_inst_3446_, 0);
v_toFunctor_3453_ = lean_ctor_get(v_toApplicative_3452_, 0);
lean_inc_ref(v_toFunctor_3453_);
v_toBind_3454_ = lean_ctor_get(v_inst_3446_, 1);
lean_inc(v_toBind_3454_);
lean_dec_ref(v_inst_3446_);
v_map_3455_ = lean_ctor_get(v_toFunctor_3453_, 0);
lean_inc(v_map_3455_);
lean_dec_ref(v_toFunctor_3453_);
v___f_3456_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3457_ = lean_box(v_text_3449_);
v___x_3458_ = lean_box(v_exe_3450_);
v___x_3459_ = lean_box(v_useLocalFile_3451_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3460_, 0, v_file_3447_);
lean_closure_set(v___f_3460_, 1, v_ext_3448_);
lean_closure_set(v___f_3460_, 2, v___x_3457_);
lean_closure_set(v___f_3460_, 3, v___x_3458_);
lean_closure_set(v___f_3460_, 4, v___x_3459_);
lean_closure_set(v___f_3460_, 5, v_inst_3445_);
v___x_3461_ = lean_apply_4(v_map_3455_, lean_box(0), lean_box(0), v___f_3456_, v_inst_3444_);
v___x_3462_ = lean_apply_4(v_toBind_3454_, lean_box(0), lean_box(0), v___x_3461_, v___f_3460_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_file_3467_, lean_object* v_ext_3468_, lean_object* v_text_3469_, lean_object* v_exe_3470_, lean_object* v_useLocalFile_3471_){
_start:
{
uint8_t v_text_boxed_3472_; uint8_t v_exe_boxed_3473_; uint8_t v_useLocalFile_boxed_3474_; lean_object* v_res_3475_; 
v_text_boxed_3472_ = lean_unbox(v_text_3469_);
v_exe_boxed_3473_ = lean_unbox(v_exe_3470_);
v_useLocalFile_boxed_3474_ = lean_unbox(v_useLocalFile_3471_);
v_res_3475_ = l_Lake_cacheArtifact(v_m_3463_, v_inst_3464_, v_inst_3465_, v_inst_3466_, v_file_3467_, v_ext_3468_, v_text_boxed_3472_, v_exe_boxed_3473_, v_useLocalFile_boxed_3474_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3477_, lean_object* v_x2_3478_){
_start:
{
lean_object* v_message_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_message_3479_ = lean_ctor_get(v_x2_3478_, 0);
v___x_3480_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3481_ = lean_string_append(v_x1_3477_, v___x_3480_);
v___x_3482_ = lean_string_append(v___x_3481_, v_message_3479_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3483_, lean_object* v_x2_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3483_, v_x2_3484_);
lean_dec_ref(v_x2_3484_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3489_, uint64_t v_inputHash_3490_, lean_object* v_pkg_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_r_3500_; lean_object* v___y_3501_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; uint8_t v___y_3508_; lean_object* v___y_3509_; lean_object* v_toContext_3515_; lean_object* v_log_3516_; uint8_t v_action_3517_; uint8_t v_wantsRebuild_3518_; lean_object* v_trace_3519_; lean_object* v_buildTime_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3586_; 
v_toContext_3515_ = lean_ctor_get(v_a_3496_, 1);
v_log_3516_ = lean_ctor_get(v_a_3497_, 0);
v_action_3517_ = lean_ctor_get_uint8(v_a_3497_, sizeof(void*)*3);
v_wantsRebuild_3518_ = lean_ctor_get_uint8(v_a_3497_, sizeof(void*)*3 + 1);
v_trace_3519_ = lean_ctor_get(v_a_3497_, 1);
v_buildTime_3520_ = lean_ctor_get(v_a_3497_, 2);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3522_ = v_a_3497_;
v_isShared_3523_ = v_isSharedCheck_3586_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_buildTime_3520_);
lean_inc(v_trace_3519_);
lean_inc(v_log_3516_);
lean_dec(v_a_3497_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3586_;
goto v_resetjp_3521_;
}
v___jp_3499_:
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_r_3500_);
lean_ctor_set(v___x_3502_, 1, v___y_3501_);
return v___x_3502_;
}
v___jp_3503_:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3510_ = 0;
v___x_3511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3511_, 0, v___y_3509_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*1, v___x_3510_);
v___x_3512_ = lean_array_push(v___y_3505_, v___x_3511_);
v___x_3513_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v___y_3506_);
lean_ctor_set(v___x_3513_, 2, v___y_3507_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*3, v___y_3508_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*3 + 1, v___y_3504_);
v___x_3514_ = lean_box(0);
v_r_3500_ = v___x_3514_;
v___y_3501_ = v___x_3513_;
goto v___jp_3499_;
}
v_resetjp_3521_:
{
lean_object* v_lakeCache_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___f_3527_; lean_object* v_a_3529_; lean_object* v_log_3530_; uint8_t v_action_3531_; uint8_t v_wantsRebuild_3532_; lean_object* v_trace_3533_; lean_object* v_buildTime_3534_; 
v_lakeCache_3524_ = lean_ctor_get(v_toContext_3515_, 2);
v___x_3525_ = l_Lake_Package_cacheScope(v_pkg_3491_);
lean_inc_ref(v_lakeCache_3524_);
v___x_3526_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3524_, v___x_3525_, v_inputHash_3490_, v_log_3516_);
v___f_3527_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; 
v_a_3560_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3560_);
v_a_3561_ = lean_ctor_get(v___x_3526_, 1);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3526_, 2);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v_a_3561_);
v___x_3563_ = v___x_3522_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3561_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_trace_3519_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_buildTime_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*3, v_action_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*3 + 1, v_wantsRebuild_3518_);
v___x_3563_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
if (lean_obj_tag(v_a_3560_) == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref(v_a_3492_);
lean_dec_ref(v_inst_3489_);
v___x_3564_ = lean_box(0);
v_r_3500_ = v___x_3564_;
v___y_3501_ = v___x_3563_;
goto v___jp_3499_;
}
else
{
lean_object* v_val_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3582_; 
v_val_3565_ = lean_ctor_get(v_a_3560_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3560_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3567_ = v_a_3560_;
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_val_3565_);
lean_dec(v_a_3560_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; 
lean_inc_ref(v_a_3496_);
lean_inc(v_a_3495_);
lean_inc(v_a_3494_);
lean_inc(v_a_3493_);
v___x_3569_ = lean_apply_8(v_inst_3489_, v_val_3565_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v___x_3563_, lean_box(0));
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v_a_3571_; lean_object* v___x_3573_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
v_a_3571_ = lean_ctor_get(v___x_3569_, 1);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3569_, 2);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v_a_3570_);
v___x_3573_ = v___x_3567_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3570_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
v_r_3500_ = v___x_3573_;
v___y_3501_ = v_a_3571_;
goto v___jp_3499_;
}
}
else
{
lean_object* v_a_3575_; lean_object* v_a_3576_; lean_object* v_log_3577_; uint8_t v_action_3578_; uint8_t v_wantsRebuild_3579_; lean_object* v_trace_3580_; lean_object* v_buildTime_3581_; 
lean_del_object(v___x_3567_);
v_a_3575_ = lean_ctor_get(v___x_3569_, 1);
lean_inc(v_a_3575_);
v_a_3576_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3569_, 2);
v_log_3577_ = lean_ctor_get(v_a_3575_, 0);
lean_inc_ref(v_log_3577_);
v_action_3578_ = lean_ctor_get_uint8(v_a_3575_, sizeof(void*)*3);
v_wantsRebuild_3579_ = lean_ctor_get_uint8(v_a_3575_, sizeof(void*)*3 + 1);
v_trace_3580_ = lean_ctor_get(v_a_3575_, 1);
lean_inc_ref(v_trace_3580_);
v_buildTime_3581_ = lean_ctor_get(v_a_3575_, 2);
lean_inc(v_buildTime_3581_);
lean_dec(v_a_3575_);
v_a_3529_ = v_a_3576_;
v_log_3530_ = v_log_3577_;
v_action_3531_ = v_action_3578_;
v_wantsRebuild_3532_ = v_wantsRebuild_3579_;
v_trace_3533_ = v_trace_3580_;
v_buildTime_3534_ = v_buildTime_3581_;
goto v___jp_3528_;
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v_a_3585_; 
lean_del_object(v___x_3522_);
lean_dec_ref(v_a_3492_);
lean_dec_ref(v_inst_3489_);
v_a_3584_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3584_);
v_a_3585_ = lean_ctor_get(v___x_3526_, 1);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3526_, 2);
v_a_3529_ = v_a_3584_;
v_log_3530_ = v_a_3585_;
v_action_3531_ = v_action_3517_;
v_wantsRebuild_3532_ = v_wantsRebuild_3518_;
v_trace_3533_ = v_trace_3519_;
v_buildTime_3534_ = v_buildTime_3520_;
goto v___jp_3528_;
}
v___jp_3528_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v___x_3535_ = lean_array_get_size(v_log_3530_);
lean_inc(v_a_3529_);
v___x_3536_ = l_Array_extract___redArg(v_log_3530_, v_a_3529_, v___x_3535_);
v___x_3537_ = l_Array_shrink___redArg(v_log_3530_, v_a_3529_);
lean_dec(v_a_3529_);
v___x_3538_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3539_ = l_Lake_lowerHexUInt64(v_inputHash_3490_);
v___x_3540_ = lean_unsigned_to_nat(7u);
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = lean_string_utf8_byte_size(v___x_3539_);
lean_inc_ref(v___x_3539_);
v___x_3543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3539_);
lean_ctor_set(v___x_3543_, 1, v___x_3541_);
lean_ctor_set(v___x_3543_, 2, v___x_3542_);
v___x_3544_ = l_String_Slice_Pos_nextn(v___x_3543_, v___x_3541_, v___x_3540_);
lean_dec_ref_known(v___x_3543_, 3);
v___x_3545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3539_);
lean_ctor_set(v___x_3545_, 1, v___x_3541_);
lean_ctor_set(v___x_3545_, 2, v___x_3544_);
v___x_3546_ = l_String_Slice_toString(v___x_3545_);
lean_dec_ref_known(v___x_3545_, 3);
v___x_3547_ = lean_string_append(v___x_3538_, v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3549_ = lean_string_append(v___x_3547_, v___x_3548_);
v___x_3550_ = lean_array_get_size(v___x_3536_);
v___x_3551_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3552_ = lean_nat_dec_lt(v___x_3541_, v___x_3550_);
if (v___x_3552_ == 0)
{
lean_dec_ref(v___x_3536_);
v___y_3504_ = v_wantsRebuild_3532_;
v___y_3505_ = v___x_3537_;
v___y_3506_ = v_trace_3533_;
v___y_3507_ = v_buildTime_3534_;
v___y_3508_ = v_action_3531_;
v___y_3509_ = v___x_3549_;
goto v___jp_3503_;
}
else
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_nat_dec_le(v___x_3550_, v___x_3550_);
if (v___x_3553_ == 0)
{
if (v___x_3552_ == 0)
{
lean_dec_ref(v___x_3536_);
v___y_3504_ = v_wantsRebuild_3532_;
v___y_3505_ = v___x_3537_;
v___y_3506_ = v_trace_3533_;
v___y_3507_ = v_buildTime_3534_;
v___y_3508_ = v_action_3531_;
v___y_3509_ = v___x_3549_;
goto v___jp_3503_;
}
else
{
size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = lean_usize_of_nat(v___x_3550_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3551_, v___f_3527_, v___x_3536_, v___x_3554_, v___x_3555_, v___x_3549_);
v___y_3504_ = v_wantsRebuild_3532_;
v___y_3505_ = v___x_3537_;
v___y_3506_ = v_trace_3533_;
v___y_3507_ = v_buildTime_3534_;
v___y_3508_ = v_action_3531_;
v___y_3509_ = v___x_3556_;
goto v___jp_3503_;
}
}
else
{
size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = lean_usize_of_nat(v___x_3550_);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3551_, v___f_3527_, v___x_3536_, v___x_3557_, v___x_3558_, v___x_3549_);
v___y_3504_ = v_wantsRebuild_3532_;
v___y_3505_ = v___x_3537_;
v___y_3506_ = v_trace_3533_;
v___y_3507_ = v_buildTime_3534_;
v___y_3508_ = v_action_3531_;
v___y_3509_ = v___x_3559_;
goto v___jp_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3587_, lean_object* v_inputHash_3588_, lean_object* v_pkg_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
uint64_t v_inputHash_boxed_3597_; lean_object* v_res_3598_; 
v_inputHash_boxed_3597_ = lean_unbox_uint64(v_inputHash_3588_);
lean_dec_ref(v_inputHash_3588_);
v_res_3598_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3587_, v_inputHash_boxed_3597_, v_pkg_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec(v_a_3591_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3599_, lean_object* v_inst_3600_, uint64_t v_inputHash_3601_, lean_object* v_pkg_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3600_, v_inputHash_3601_, v_pkg_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3611_, lean_object* v_inst_3612_, lean_object* v_inputHash_3613_, lean_object* v_pkg_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
uint64_t v_inputHash_boxed_3622_; lean_object* v_res_3623_; 
v_inputHash_boxed_3622_ = lean_unbox_uint64(v_inputHash_3613_);
lean_dec_ref(v_inputHash_3613_);
v_res_3623_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3611_, v_inst_3612_, v_inputHash_boxed_3622_, v_pkg_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec(v_a_3616_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3624_, lean_object* v_____r_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3633_, 0, v_a_3624_);
v___x_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___y_3631_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3636_, lean_object* v_____r_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3636_, v_____r_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3647_, uint64_t v_inputHash_3648_, lean_object* v_savedTrace_3649_, lean_object* v_pkg_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___y_3659_; lean_object* v_a_3663_; lean_object* v_a_3664_; lean_object* v___y_3679_; 
if (lean_obj_tag(v_savedTrace_3649_) == 2)
{
lean_object* v_data_3694_; uint64_t v_depHash_3695_; lean_object* v_outputs_x3f_3696_; uint8_t v___x_3697_; 
v_data_3694_ = lean_ctor_get(v_savedTrace_3649_, 0);
lean_inc_ref(v_data_3694_);
lean_dec_ref_known(v_savedTrace_3649_, 1);
v_depHash_3695_ = lean_ctor_get_uint64(v_data_3694_, sizeof(void*)*3);
v_outputs_x3f_3696_ = lean_ctor_get(v_data_3694_, 1);
lean_inc(v_outputs_x3f_3696_);
lean_dec_ref(v_data_3694_);
v___x_3697_ = lean_uint64_dec_eq(v_depHash_3695_, v_inputHash_3648_);
if (v___x_3697_ == 0)
{
lean_dec(v_outputs_x3f_3696_);
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_pkg_3650_);
lean_dec_ref(v_inst_3647_);
v___y_3659_ = v_a_3656_;
goto v___jp_3658_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3696_) == 1)
{
lean_object* v_val_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_val_3698_ = lean_ctor_get(v_outputs_x3f_3696_, 0);
lean_inc_n(v_val_3698_, 2);
lean_dec_ref_known(v_outputs_x3f_3696_, 1);
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3700_, 0, v_val_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
lean_ctor_set(v___x_3700_, 2, v___x_3699_);
lean_inc_ref(v_a_3655_);
lean_inc(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc(v_a_3652_);
lean_inc_ref(v_a_3651_);
v___x_3701_ = lean_apply_8(v_inst_3647_, v___x_3700_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, lean_box(0));
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_config_3702_; lean_object* v_a_3703_; lean_object* v_a_3704_; lean_object* v_enableArtifactCache_x3f_3705_; lean_object* v_a_3707_; uint8_t v_a_3711_; lean_object* v_a_3712_; 
v_config_3702_ = lean_ctor_get(v_pkg_3650_, 6);
v_a_3703_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3703_);
v_a_3704_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3701_, 2);
v_enableArtifactCache_x3f_3705_ = lean_ctor_get(v_config_3702_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3705_) == 0)
{
lean_object* v_toContext_3744_; lean_object* v_lakeEnv_3745_; lean_object* v_enableArtifactCache_x3f_3746_; 
v_toContext_3744_ = lean_ctor_get(v_a_3655_, 1);
v_lakeEnv_3745_ = lean_ctor_get(v_toContext_3744_, 0);
v_enableArtifactCache_x3f_3746_ = lean_ctor_get(v_lakeEnv_3745_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3746_) == 0)
{
lean_object* v_packages_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v_config_3750_; lean_object* v_enableArtifactCache_x3f_3751_; 
v_packages_3747_ = lean_ctor_get(v_toContext_3744_, 4);
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = lean_array_fget_borrowed(v_packages_3747_, v___x_3748_);
v_config_3750_ = lean_ctor_get(v___x_3749_, 6);
v_enableArtifactCache_x3f_3751_ = lean_ctor_get(v_config_3750_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3751_) == 0)
{
lean_dec(v_val_3698_);
lean_dec_ref(v_pkg_3650_);
v_a_3707_ = v_a_3704_;
goto v___jp_3706_;
}
else
{
lean_object* v_val_3752_; uint8_t v___x_3753_; 
v_val_3752_ = lean_ctor_get(v_enableArtifactCache_x3f_3751_, 0);
v___x_3753_ = lean_unbox(v_val_3752_);
v_a_3711_ = v___x_3753_;
v_a_3712_ = v_a_3704_;
goto v___jp_3710_;
}
}
else
{
lean_object* v_val_3754_; uint8_t v___x_3755_; 
v_val_3754_ = lean_ctor_get(v_enableArtifactCache_x3f_3746_, 0);
v___x_3755_ = lean_unbox(v_val_3754_);
v_a_3711_ = v___x_3755_;
v_a_3712_ = v_a_3704_;
goto v___jp_3710_;
}
}
else
{
lean_object* v_val_3756_; uint8_t v___x_3757_; 
v_val_3756_ = lean_ctor_get(v_enableArtifactCache_x3f_3705_, 0);
v___x_3757_ = lean_unbox(v_val_3756_);
v_a_3711_ = v___x_3757_;
v_a_3712_ = v_a_3704_;
goto v___jp_3710_;
}
v___jp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = lean_box(0);
v___x_3709_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3703_, v___x_3708_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3707_);
lean_dec_ref(v_a_3651_);
v___y_3679_ = v___x_3709_;
goto v___jp_3678_;
}
v___jp_3710_:
{
if (v_a_3711_ == 0)
{
lean_dec(v_val_3698_);
lean_dec_ref(v_pkg_3650_);
v_a_3707_ = v_a_3712_;
goto v___jp_3706_;
}
else
{
lean_object* v_toContext_3713_; lean_object* v_log_3714_; uint8_t v_action_3715_; uint8_t v_wantsRebuild_3716_; lean_object* v_trace_3717_; lean_object* v_buildTime_3718_; lean_object* v_lakeCache_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v_toContext_3713_ = lean_ctor_get(v_a_3655_, 1);
v_log_3714_ = lean_ctor_get(v_a_3712_, 0);
v_action_3715_ = lean_ctor_get_uint8(v_a_3712_, sizeof(void*)*3);
v_wantsRebuild_3716_ = lean_ctor_get_uint8(v_a_3712_, sizeof(void*)*3 + 1);
v_trace_3717_ = lean_ctor_get(v_a_3712_, 1);
v_buildTime_3718_ = lean_ctor_get(v_a_3712_, 2);
v_lakeCache_3719_ = lean_ctor_get(v_toContext_3713_, 2);
v___x_3720_ = l_Lake_Package_cacheScope(v_pkg_3650_);
v___x_3721_ = 0;
lean_inc_ref(v_lakeCache_3719_);
v___x_3722_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3719_, v___x_3720_, v_inputHash_3648_, v_val_3698_, v___x_3699_, v___x_3699_, v___x_3721_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref_known(v___x_3722_, 1);
v___x_3723_ = lean_box(0);
v___x_3724_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3703_, v___x_3723_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3712_);
lean_dec_ref(v_a_3651_);
v___y_3679_ = v___x_3724_;
goto v___jp_3678_;
}
else
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3740_; 
lean_inc(v_buildTime_3718_);
lean_inc_ref(v_trace_3717_);
lean_inc_ref(v_log_3714_);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3712_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3741_ = lean_ctor_get(v_a_3712_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_a_3712_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_a_3712_, 0);
lean_dec(v_unused_3743_);
v___x_3726_ = v_a_3712_;
v_isShared_3727_ = v_isSharedCheck_3740_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v_a_3712_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3740_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3737_; 
v_a_3728_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3729_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3730_ = lean_io_error_to_string(v_a_3728_);
v___x_3731_ = lean_string_append(v___x_3729_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = 2;
v___x_3733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set_uint8(v___x_3733_, sizeof(void*)*1, v___x_3732_);
v___x_3734_ = lean_box(0);
v___x_3735_ = lean_array_push(v_log_3714_, v___x_3733_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3735_);
v___x_3737_ = v___x_3726_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_trace_3717_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_buildTime_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, sizeof(void*)*3, v_action_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, sizeof(void*)*3 + 1, v_wantsRebuild_3716_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3703_, v___x_3734_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v___x_3737_);
lean_dec_ref(v_a_3651_);
v___y_3679_ = v___x_3738_;
goto v___jp_3678_;
}
}
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v_a_3759_; 
lean_dec(v_val_3698_);
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_pkg_3650_);
v_a_3758_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3758_);
v_a_3759_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3701_, 2);
v_a_3663_ = v_a_3758_;
v_a_3664_ = v_a_3759_;
goto v___jp_3662_;
}
}
else
{
lean_dec(v_outputs_x3f_3696_);
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_pkg_3650_);
lean_dec_ref(v_inst_3647_);
v___y_3659_ = v_a_3656_;
goto v___jp_3658_;
}
}
}
else
{
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_pkg_3650_);
lean_dec(v_savedTrace_3649_);
lean_dec_ref(v_inst_3647_);
v___y_3659_ = v_a_3656_;
goto v___jp_3658_;
}
v___jp_3658_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___y_3659_);
return v___x_3661_;
}
v___jp_3662_:
{
lean_object* v_log_3665_; uint8_t v_action_3666_; uint8_t v_wantsRebuild_3667_; lean_object* v_trace_3668_; lean_object* v_buildTime_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3677_; 
v_log_3665_ = lean_ctor_get(v_a_3664_, 0);
v_action_3666_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*3);
v_wantsRebuild_3667_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*3 + 1);
v_trace_3668_ = lean_ctor_get(v_a_3664_, 1);
v_buildTime_3669_ = lean_ctor_get(v_a_3664_, 2);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3671_ = v_a_3664_;
v_isShared_3672_ = v_isSharedCheck_3677_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_buildTime_3669_);
lean_inc(v_trace_3668_);
lean_inc(v_log_3665_);
lean_dec(v_a_3664_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3677_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = l_Array_shrink___redArg(v_log_3665_, v_a_3663_);
lean_dec(v_a_3663_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3673_);
v___x_3675_ = v___x_3671_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_trace_3668_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_buildTime_3669_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*3, v_action_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*3 + 1, v_wantsRebuild_3667_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
v___y_3659_ = v___x_3675_;
goto v___jp_3658_;
}
}
}
v___jp_3678_:
{
if (lean_obj_tag(v___y_3679_) == 0)
{
lean_object* v_a_3680_; 
v_a_3680_ = lean_ctor_get(v___y_3679_, 0);
if (lean_obj_tag(v_a_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3689_; 
lean_inc_ref(v_a_3680_);
v_a_3681_ = lean_ctor_get(v___y_3679_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___y_3679_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___y_3679_, 0);
lean_dec(v_unused_3690_);
v___x_3683_ = v___y_3679_;
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___y_3679_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v_a_3685_; lean_object* v___x_3687_; 
v_a_3685_ = lean_ctor_get(v_a_3680_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v_a_3680_, 1);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_a_3685_);
v___x_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3685_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_a_3681_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_a_3691_; 
v_a_3691_ = lean_ctor_get(v___y_3679_, 1);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___y_3679_, 2);
v___y_3659_ = v_a_3691_;
goto v___jp_3658_;
}
}
else
{
lean_object* v_a_3692_; lean_object* v_a_3693_; 
v_a_3692_ = lean_ctor_get(v___y_3679_, 0);
lean_inc(v_a_3692_);
v_a_3693_ = lean_ctor_get(v___y_3679_, 1);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___y_3679_, 2);
v_a_3663_ = v_a_3692_;
v_a_3664_ = v_a_3693_;
goto v___jp_3662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3760_, lean_object* v_inputHash_3761_, lean_object* v_savedTrace_3762_, lean_object* v_pkg_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
uint64_t v_inputHash_boxed_3771_; lean_object* v_res_3772_; 
v_inputHash_boxed_3771_ = lean_unbox_uint64(v_inputHash_3761_);
lean_dec_ref(v_inputHash_3761_);
v_res_3772_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3760_, v_inputHash_boxed_3771_, v_savedTrace_3762_, v_pkg_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec(v_a_3765_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3773_, lean_object* v_inst_3774_, uint64_t v_inputHash_3775_, lean_object* v_savedTrace_3776_, lean_object* v_pkg_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3774_, v_inputHash_3775_, v_savedTrace_3776_, v_pkg_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3786_, lean_object* v_inst_3787_, lean_object* v_inputHash_3788_, lean_object* v_savedTrace_3789_, lean_object* v_pkg_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
uint64_t v_inputHash_boxed_3798_; lean_object* v_res_3799_; 
v_inputHash_boxed_3798_ = lean_unbox_uint64(v_inputHash_3788_);
lean_dec_ref(v_inputHash_3788_);
v_res_3799_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3786_, v_inst_3787_, v_inputHash_boxed_3798_, v_savedTrace_3789_, v_pkg_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec(v_a_3792_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3800_, uint64_t v_inputHash_3801_, lean_object* v_savedTrace_3802_, lean_object* v_pkg_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_a_3812_; lean_object* v___y_3813_; lean_object* v___x_3816_; lean_object* v_a_3817_; 
lean_inc_ref(v_a_3804_);
lean_inc_ref(v_pkg_3803_);
lean_inc_ref(v_inst_3800_);
v___x_3816_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3800_, v_inputHash_3801_, v_savedTrace_3802_, v_pkg_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
if (lean_obj_tag(v_a_3817_) == 1)
{
lean_object* v_a_3818_; lean_object* v_val_3819_; 
lean_dec_ref(v_a_3804_);
lean_dec_ref(v_pkg_3803_);
lean_dec_ref(v_inst_3800_);
v_a_3818_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3816_);
v_val_3819_ = lean_ctor_get(v_a_3817_, 0);
lean_inc(v_val_3819_);
lean_dec_ref_known(v_a_3817_, 1);
v_a_3812_ = v_val_3819_;
v___y_3813_ = v_a_3818_;
goto v___jp_3811_;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v_a_3822_; 
lean_dec(v_a_3817_);
v_a_3820_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3816_);
v___x_3821_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3800_, v_inputHash_3801_, v_pkg_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3820_);
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
if (lean_obj_tag(v_a_3822_) == 1)
{
lean_object* v_a_3823_; lean_object* v_val_3824_; 
v_a_3823_ = lean_ctor_get(v___x_3821_, 1);
lean_inc(v_a_3823_);
lean_dec_ref(v___x_3821_);
v_val_3824_ = lean_ctor_get(v_a_3822_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_a_3822_, 1);
v_a_3812_ = v_val_3824_;
v___y_3813_ = v_a_3823_;
goto v___jp_3811_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v_a_3822_);
v_a_3825_ = lean_ctor_get(v___x_3821_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v___x_3821_, 0);
lean_dec(v_unused_3834_);
v___x_3827_ = v___x_3821_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3821_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_box(0);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3829_);
v___x_3831_ = v___x_3827_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_a_3825_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
v___jp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3814_, 0, v_a_3812_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___y_3813_);
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3835_, lean_object* v_inputHash_3836_, lean_object* v_savedTrace_3837_, lean_object* v_pkg_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
uint64_t v_inputHash_boxed_3846_; lean_object* v_res_3847_; 
v_inputHash_boxed_3846_ = lean_unbox_uint64(v_inputHash_3836_);
lean_dec_ref(v_inputHash_3836_);
v_res_3847_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3835_, v_inputHash_boxed_3846_, v_savedTrace_3837_, v_pkg_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec(v_a_3840_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3848_, lean_object* v_inst_3849_, uint64_t v_inputHash_3850_, lean_object* v_savedTrace_3851_, lean_object* v_pkg_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v_a_3861_; lean_object* v___y_3862_; lean_object* v___x_3865_; lean_object* v_a_3866_; 
lean_inc_ref(v_a_3853_);
lean_inc_ref(v_pkg_3852_);
lean_inc_ref(v_inst_3849_);
v___x_3865_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3849_, v_inputHash_3850_, v_savedTrace_3851_, v_pkg_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
if (lean_obj_tag(v_a_3866_) == 1)
{
lean_object* v_a_3867_; lean_object* v_val_3868_; 
lean_dec_ref(v_a_3853_);
lean_dec_ref(v_pkg_3852_);
lean_dec_ref(v_inst_3849_);
v_a_3867_ = lean_ctor_get(v___x_3865_, 1);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3865_);
v_val_3868_ = lean_ctor_get(v_a_3866_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v_a_3866_, 1);
v_a_3861_ = v_val_3868_;
v___y_3862_ = v_a_3867_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v_a_3871_; 
lean_dec(v_a_3866_);
v_a_3869_ = lean_ctor_get(v___x_3865_, 1);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3865_);
v___x_3870_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3849_, v_inputHash_3850_, v_pkg_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3869_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
if (lean_obj_tag(v_a_3871_) == 1)
{
lean_object* v_a_3872_; lean_object* v_val_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3870_);
v_val_3873_ = lean_ctor_get(v_a_3871_, 0);
lean_inc(v_val_3873_);
lean_dec_ref_known(v_a_3871_, 1);
v_a_3861_ = v_val_3873_;
v___y_3862_ = v_a_3872_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_a_3871_);
v_a_3874_ = lean_ctor_get(v___x_3870_, 1);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; 
v_unused_3883_ = lean_ctor_get(v___x_3870_, 0);
lean_dec(v_unused_3883_);
v___x_3876_ = v___x_3870_;
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3870_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = lean_box(0);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3878_);
v___x_3880_ = v___x_3876_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_a_3874_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
v___jp_3860_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_a_3861_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___y_3862_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_inst_3885_, lean_object* v_inputHash_3886_, lean_object* v_savedTrace_3887_, lean_object* v_pkg_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
uint64_t v_inputHash_boxed_3896_; lean_object* v_res_3897_; 
v_inputHash_boxed_3896_ = lean_unbox_uint64(v_inputHash_3886_);
lean_dec_ref(v_inputHash_3886_);
v_res_3897_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3884_, v_inst_3885_, v_inputHash_boxed_3896_, v_savedTrace_3887_, v_pkg_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec(v_a_3890_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3898_, lean_object* v___x_3899_, lean_object* v_mtime_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_inc_ref(v___x_3899_);
v___x_3908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3908_, 0, v_descr_3898_);
lean_ctor_set(v___x_3908_, 1, v___x_3899_);
lean_ctor_set(v___x_3908_, 2, v___x_3899_);
lean_ctor_set(v___x_3908_, 3, v_mtime_3900_);
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
lean_ctor_set(v___x_3909_, 1, v___y_3906_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3910_, lean_object* v___x_3911_, lean_object* v_mtime_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lake_resolveArtifact___lam__0(v_descr_3910_, v___x_3911_, v_mtime_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3922_, lean_object* v___f_3923_, lean_object* v_____r_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_log_3932_; uint8_t v_action_3933_; uint8_t v_wantsRebuild_3934_; lean_object* v_trace_3935_; lean_object* v_buildTime_3936_; lean_object* v___x_3937_; 
v_log_3932_ = lean_ctor_get(v___y_3930_, 0);
v_action_3933_ = lean_ctor_get_uint8(v___y_3930_, sizeof(void*)*3);
v_wantsRebuild_3934_ = lean_ctor_get_uint8(v___y_3930_, sizeof(void*)*3 + 1);
v_trace_3935_ = lean_ctor_get(v___y_3930_, 1);
v_buildTime_3936_ = lean_ctor_get(v___y_3930_, 2);
v___x_3937_ = lean_io_metadata(v___x_3922_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v_modified_3939_; lean_object* v___x_3940_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v_modified_3939_ = lean_ctor_get(v_a_3938_, 1);
lean_inc_ref(v_modified_3939_);
lean_dec(v_a_3938_);
lean_inc_ref(v___y_3929_);
lean_inc(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
v___x_3940_ = lean_apply_8(v___f_3923_, v_modified_3939_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, lean_box(0));
return v___x_3940_;
}
else
{
lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3956_; 
lean_inc(v_buildTime_3936_);
lean_inc_ref(v_trace_3935_);
lean_inc_ref(v_log_3932_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v___f_3923_);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___y_3930_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; 
v_unused_3957_ = lean_ctor_get(v___y_3930_, 2);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v___y_3930_, 1);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v___y_3930_, 0);
lean_dec(v_unused_3959_);
v___x_3942_ = v___y_3930_;
v_isShared_3943_ = v_isSharedCheck_3956_;
goto v_resetjp_3941_;
}
else
{
lean_dec(v___y_3930_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3956_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_a_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
v_a_3944_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3945_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3946_ = lean_io_error_to_string(v_a_3944_);
v___x_3947_ = lean_string_append(v___x_3945_, v___x_3946_);
lean_dec_ref(v___x_3946_);
v___x_3948_ = 3;
v___x_3949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set_uint8(v___x_3949_, sizeof(void*)*1, v___x_3948_);
v___x_3950_ = lean_array_get_size(v_log_3932_);
v___x_3951_ = lean_array_push(v_log_3932_, v___x_3949_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3951_);
v___x_3953_ = v___x_3942_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_trace_3935_);
lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_buildTime_3936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3955_, sizeof(void*)*3, v_action_3933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3955_, sizeof(void*)*3 + 1, v_wantsRebuild_3934_);
v___x_3953_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; 
v___x_3954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3950_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
return v___x_3954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3960_, lean_object* v___f_3961_, lean_object* v_____r_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lake_resolveArtifact___lam__1(v___x_3960_, v___f_3961_, v_____r_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___x_3960_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3982_, lean_object* v_service_x3f_3983_, lean_object* v_scope_x3f_3984_, uint8_t v_exe_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v___y_3994_; lean_object* v_a_3995_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v_toContext_4001_; lean_object* v_log_4002_; uint8_t v_action_4003_; uint8_t v_wantsRebuild_4004_; lean_object* v_trace_4005_; lean_object* v_buildTime_4006_; lean_object* v_lakeConfig_4007_; lean_object* v_lakeCache_4008_; uint64_t v_hash_4009_; lean_object* v_ext_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___y_4014_; lean_object* v___x_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; 
v_toContext_4001_ = lean_ctor_get(v_a_3990_, 1);
v_log_4002_ = lean_ctor_get(v_a_3991_, 0);
v_action_4003_ = lean_ctor_get_uint8(v_a_3991_, sizeof(void*)*3);
v_wantsRebuild_4004_ = lean_ctor_get_uint8(v_a_3991_, sizeof(void*)*3 + 1);
v_trace_4005_ = lean_ctor_get(v_a_3991_, 1);
v_buildTime_4006_ = lean_ctor_get(v_a_3991_, 2);
v_lakeConfig_4007_ = lean_ctor_get(v_toContext_4001_, 1);
v_lakeCache_4008_ = lean_ctor_get(v_toContext_4001_, 2);
v_hash_4009_ = lean_ctor_get_uint64(v_descr_3982_, sizeof(void*)*1);
v_ext_4010_ = lean_ctor_get(v_descr_3982_, 0);
v___x_4011_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4008_);
v___x_4012_ = l_System_FilePath_join(v_lakeCache_4008_, v___x_4011_);
v___x_4112_ = lean_string_utf8_byte_size(v_ext_4010_);
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = lean_nat_dec_eq(v___x_4112_, v___x_4113_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4115_ = l_Lake_lowerHexUInt64(v_hash_4009_);
v___x_4116_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
v___x_4118_ = lean_string_append(v___x_4117_, v_ext_4010_);
v___y_4014_ = v___x_4118_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lake_lowerHexUInt64(v_hash_4009_);
v___y_4014_ = v___x_4119_;
goto v___jp_4013_;
}
v___jp_3993_:
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___y_3994_);
lean_ctor_set(v___x_3996_, 1, v_a_3995_);
return v___x_3996_;
}
v___jp_3997_:
{
if (lean_obj_tag(v___y_3999_) == 0)
{
lean_dec(v___y_3998_);
return v___y_3999_;
}
else
{
lean_object* v_a_4000_; 
v_a_4000_ = lean_ctor_get(v___y_3999_, 1);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___y_3999_, 2);
v___y_3994_ = v___y_3998_;
v_a_3995_ = v_a_4000_;
goto v___jp_3993_;
}
}
v___jp_4013_:
{
lean_object* v___x_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; 
v___x_4015_ = l_Lake_joinRelative(v___x_4012_, v___y_4014_);
lean_inc_ref(v___x_4015_);
lean_inc_ref(v_descr_3982_);
v___f_4016_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4016_, 0, v_descr_3982_);
lean_closure_set(v___f_4016_, 1, v___x_4015_);
v___x_4017_ = lean_io_metadata(v___x_4015_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v_modified_4019_; lean_object* v___x_4020_; 
lean_dec_ref(v___f_4016_);
lean_dec(v_scope_x3f_3984_);
lean_dec(v_service_x3f_3983_);
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___x_4017_, 1);
v_modified_4019_ = lean_ctor_get(v_a_4018_, 1);
lean_inc_ref(v_modified_4019_);
lean_dec(v_a_4018_);
v___x_4020_ = l_Lake_resolveArtifact___lam__0(v_descr_3982_, v___x_4015_, v_modified_4019_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
lean_dec_ref(v_a_3986_);
return v___x_4020_;
}
else
{
lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4108_; 
lean_inc(v_buildTime_4006_);
lean_inc_ref(v_trace_4005_);
lean_inc_ref(v_log_4002_);
lean_dec_ref(v_descr_3982_);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_a_3991_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; lean_object* v_unused_4110_; lean_object* v_unused_4111_; 
v_unused_4109_ = lean_ctor_get(v_a_3991_, 2);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_a_3991_, 1);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_a_3991_, 0);
lean_dec(v_unused_4111_);
v___x_4022_ = v_a_3991_;
v_isShared_4023_ = v_isSharedCheck_4108_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v_a_3991_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4108_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v_a_4024_; 
v_a_4024_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4017_, 1);
if (lean_obj_tag(v_a_4024_) == 11)
{
lean_object* v___x_4025_; 
lean_dec_ref_known(v_a_4024_, 2);
v___x_4025_ = lean_array_get_size(v_log_4002_);
if (lean_obj_tag(v_service_x3f_3983_) == 1)
{
lean_object* v_val_4026_; lean_object* v_cacheServices_4027_; uint8_t v___x_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_val_4026_ = lean_ctor_get(v_service_x3f_3983_, 0);
lean_inc_n(v_val_4026_, 2);
lean_dec_ref_known(v_service_x3f_3983_, 1);
v_cacheServices_4027_ = lean_ctor_get(v_lakeConfig_4007_, 3);
v___x_4028_ = 4;
v___x_4029_ = l_Lake_JobAction_merge(v_action_4003_, v___x_4028_);
v___x_4030_ = lean_box(0);
v___x_4031_ = l_Lean_Name_str___override(v___x_4030_, v_val_4026_);
v___x_4032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4027_, v___x_4031_);
lean_dec(v___x_4031_);
if (lean_obj_tag(v___x_4032_) == 1)
{
lean_dec(v_val_4026_);
if (lean_obj_tag(v_scope_x3f_3984_) == 1)
{
lean_object* v_val_4033_; lean_object* v_val_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_val_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v_val_4034_ = lean_ctor_get(v_scope_x3f_3984_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v_scope_x3f_3984_, 1);
v___x_4035_ = l_Lake_CacheService_artifactUrl(v_hash_4009_, v_val_4033_, v_val_4034_);
v___x_4036_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4037_ = l_Lake_lowerHexUInt64(v_hash_4009_);
v___x_4038_ = lean_string_append(v___x_4036_, v___x_4037_);
lean_dec_ref(v___x_4037_);
v___x_4039_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4040_ = lean_string_append(v___x_4038_, v___x_4039_);
v___x_4041_ = lean_string_append(v___x_4040_, v___x_4015_);
v___x_4042_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4043_ = lean_string_append(v___x_4041_, v___x_4042_);
v___x_4044_ = lean_string_append(v___x_4043_, v___x_4035_);
v___x_4045_ = 0;
v___x_4046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set_uint8(v___x_4046_, sizeof(void*)*1, v___x_4045_);
v___x_4047_ = lean_array_push(v_log_4002_, v___x_4046_);
lean_inc_ref(v___x_4015_);
v___x_4048_ = l_Lake_downloadArtifactCore(v_hash_4009_, v___x_4035_, v___x_4015_, v___x_4047_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; uint8_t v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 1);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 2);
v___x_4050_ = 1;
v___x_4051_ = 0;
v___x_4052_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4052_, 0, v___x_4050_);
lean_ctor_set_uint8(v___x_4052_, 1, v___x_4051_);
lean_ctor_set_uint8(v___x_4052_, 2, v_exe_3985_);
lean_inc_ref_n(v___x_4052_, 2);
v___x_4053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
lean_ctor_set(v___x_4053_, 2, v___x_4052_);
v___x_4054_ = l_IO_setAccessRights(v___x_4015_, v___x_4053_);
lean_dec_ref_known(v___x_4053_, 3);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v___x_4056_; 
lean_dec_ref_known(v___x_4054_, 1);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v_a_4049_);
v___x_4056_ = v___x_4022_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4049_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4059_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4056_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_ctor_set_uint8(v___x_4056_, sizeof(void*)*3, v___x_4029_);
v___x_4057_ = lean_box(0);
v___x_4058_ = l_Lake_resolveArtifact___lam__1(v___x_4015_, v___f_4016_, v___x_4057_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v___x_4056_);
lean_dec_ref(v___x_4015_);
v___y_3998_ = v___x_4025_;
v___y_3999_ = v___x_4058_;
goto v___jp_3997_;
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v_a_4060_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4054_, 1);
v___x_4061_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4062_ = lean_io_error_to_string(v_a_4060_);
v___x_4063_ = lean_string_append(v___x_4061_, v___x_4062_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = 2;
v___x_4065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4065_, 0, v___x_4063_);
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*1, v___x_4064_);
v___x_4066_ = lean_box(0);
v___x_4067_ = lean_array_push(v_a_4049_, v___x_4065_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4067_);
v___x_4069_ = v___x_4022_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4071_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4069_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*3, v___x_4029_);
v___x_4070_ = l_Lake_resolveArtifact___lam__1(v___x_4015_, v___f_4016_, v___x_4066_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v___x_4069_);
lean_dec_ref(v___x_4015_);
v___y_3998_ = v___x_4025_;
v___y_3999_ = v___x_4070_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; 
lean_dec_ref(v___f_4016_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v_a_3986_);
v_a_4072_ = lean_ctor_get(v___x_4048_, 1);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4048_, 2);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v_a_4072_);
v___x_4074_ = v___x_4022_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4072_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4075_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4075_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_ctor_set_uint8(v___x_4074_, sizeof(void*)*3, v___x_4029_);
v___y_3994_ = v___x_4025_;
v_a_3995_ = v___x_4074_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
lean_dec_ref_known(v___x_4032_, 1);
lean_dec_ref(v___f_4016_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v_a_3986_);
lean_dec(v_scope_x3f_3984_);
v___x_4076_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4077_ = lean_array_push(v_log_4002_, v___x_4076_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4077_);
v___x_4079_ = v___x_4022_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4080_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_ctor_set_uint8(v___x_4079_, sizeof(void*)*3, v___x_4029_);
v___y_3994_ = v___x_4025_;
v_a_3995_ = v___x_4079_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
lean_dec(v___x_4032_);
lean_dec_ref(v___f_4016_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v_a_3986_);
lean_dec(v_scope_x3f_3984_);
v___x_4081_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4082_ = lean_string_append(v___x_4081_, v_val_4026_);
lean_dec(v_val_4026_);
v___x_4083_ = 3;
v___x_4084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4084_, 0, v___x_4082_);
lean_ctor_set_uint8(v___x_4084_, sizeof(void*)*1, v___x_4083_);
v___x_4085_ = lean_array_push(v_log_4002_, v___x_4084_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4085_);
v___x_4087_ = v___x_4022_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4088_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_ctor_set_uint8(v___x_4087_, sizeof(void*)*3, v___x_4029_);
v___y_3994_ = v___x_4025_;
v_a_3995_ = v___x_4087_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4095_; 
lean_dec_ref(v___f_4016_);
lean_dec_ref(v_a_3986_);
lean_dec(v_scope_x3f_3984_);
lean_dec(v_service_x3f_3983_);
v___x_4089_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4090_ = lean_string_append(v___x_4089_, v___x_4015_);
lean_dec_ref(v___x_4015_);
v___x_4091_ = 3;
v___x_4092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set_uint8(v___x_4092_, sizeof(void*)*1, v___x_4091_);
v___x_4093_ = lean_array_push(v_log_4002_, v___x_4092_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4093_);
v___x_4095_ = v___x_4022_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4096_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4096_, sizeof(void*)*3, v_action_4003_);
lean_ctor_set_uint8(v_reuseFailAlloc_4096_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
v___y_3994_ = v___x_4025_;
v_a_3995_ = v___x_4095_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec_ref(v___f_4016_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v_a_3986_);
lean_dec(v_scope_x3f_3984_);
lean_dec(v_service_x3f_3983_);
v___x_4097_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4098_ = lean_io_error_to_string(v_a_4024_);
v___x_4099_ = lean_string_append(v___x_4097_, v___x_4098_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = 3;
v___x_4101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set_uint8(v___x_4101_, sizeof(void*)*1, v___x_4100_);
v___x_4102_ = lean_array_get_size(v_log_4002_);
v___x_4103_ = lean_array_push(v_log_4002_, v___x_4101_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4103_);
v___x_4105_ = v___x_4022_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_trace_4005_);
lean_ctor_set(v_reuseFailAlloc_4107_, 2, v_buildTime_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4107_, sizeof(void*)*3, v_action_4003_);
lean_ctor_set_uint8(v_reuseFailAlloc_4107_, sizeof(void*)*3 + 1, v_wantsRebuild_4004_);
v___x_4105_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4102_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
return v___x_4106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4120_, lean_object* v_service_x3f_4121_, lean_object* v_scope_x3f_4122_, lean_object* v_exe_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
uint8_t v_exe_boxed_4131_; lean_object* v_res_4132_; 
v_exe_boxed_4131_ = lean_unbox(v_exe_4123_);
v_res_4132_ = l_Lake_resolveArtifact(v_descr_4120_, v_service_x3f_4121_, v_scope_x3f_4122_, v_exe_boxed_4131_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
lean_dec_ref(v_a_4128_);
lean_dec(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec(v_a_4125_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4135_, uint8_t v_exe_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_data_4144_; lean_object* v_service_x3f_4145_; lean_object* v_scope_x3f_4146_; lean_object* v___x_4147_; 
v_data_4144_ = lean_ctor_get(v_out_4135_, 0);
lean_inc_n(v_data_4144_, 2);
v_service_x3f_4145_ = lean_ctor_get(v_out_4135_, 1);
lean_inc(v_service_x3f_4145_);
v_scope_x3f_4146_ = lean_ctor_get(v_out_4135_, 2);
lean_inc(v_scope_x3f_4146_);
lean_dec_ref(v_out_4135_);
v___x_4147_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4144_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v_log_4149_; uint8_t v_action_4150_; uint8_t v_wantsRebuild_4151_; lean_object* v_trace_4152_; lean_object* v_buildTime_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_scope_x3f_4146_);
lean_dec(v_service_x3f_4145_);
lean_dec_ref(v_a_4137_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v_log_4149_ = lean_ctor_get(v_a_4142_, 0);
v_action_4150_ = lean_ctor_get_uint8(v_a_4142_, sizeof(void*)*3);
v_wantsRebuild_4151_ = lean_ctor_get_uint8(v_a_4142_, sizeof(void*)*3 + 1);
v_trace_4152_ = lean_ctor_get(v_a_4142_, 1);
v_buildTime_4153_ = lean_ctor_get(v_a_4142_, 2);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_a_4142_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4155_ = v_a_4142_;
v_isShared_4156_ = v_isSharedCheck_4175_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_buildTime_4153_);
lean_inc(v_trace_4152_);
lean_inc(v_log_4149_);
lean_dec(v_a_4142_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4175_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4157_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4158_ = l_Lean_Json_render(v_data_4144_);
v___x_4159_ = lean_unsigned_to_nat(80u);
v___x_4160_ = lean_unsigned_to_nat(2u);
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = l_Std_Format_pretty(v___x_4158_, v___x_4159_, v___x_4160_, v___x_4161_);
v___x_4163_ = lean_string_append(v___x_4157_, v___x_4162_);
lean_dec_ref(v___x_4162_);
v___x_4164_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4165_ = lean_string_append(v___x_4163_, v___x_4164_);
v___x_4166_ = lean_string_append(v___x_4165_, v_a_4148_);
lean_dec(v_a_4148_);
v___x_4167_ = 3;
v___x_4168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*1, v___x_4167_);
v___x_4169_ = lean_array_get_size(v_log_4149_);
v___x_4170_ = lean_array_push(v_log_4149_, v___x_4168_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4170_);
v___x_4172_ = v___x_4155_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_trace_4152_);
lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_buildTime_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*3, v_action_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4174_, sizeof(void*)*3 + 1, v_wantsRebuild_4151_);
v___x_4172_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4169_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
return v___x_4173_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
lean_dec(v_data_4144_);
v_a_4176_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4177_ = l_Lake_resolveArtifact(v_a_4176_, v_service_x3f_4145_, v_scope_x3f_4146_, v_exe_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
return v___x_4177_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4178_, lean_object* v_exe_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
uint8_t v_exe_boxed_4187_; lean_object* v_res_4188_; 
v_exe_boxed_4187_ = lean_unbox(v_exe_4179_);
v_res_4188_ = l_Lake_resolveArtifactOutput(v_out_4178_, v_exe_boxed_4187_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec(v_a_4181_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4189_, lean_object* v_out_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lake_resolveArtifactOutput(v_out_4190_, v_exe_4189_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4199_, lean_object* v_out_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v_exe_boxed_4208_; lean_object* v_res_4209_; 
v_exe_boxed_4208_ = lean_unbox(v_exe_4199_);
v_res_4209_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4208_, v_out_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec(v___y_4202_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4210_){
_start:
{
lean_object* v___x_4211_; lean_object* v___f_4212_; 
v___x_4211_ = lean_box(v_exe_4210_);
v___f_4212_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4212_, 0, v___x_4211_);
return v___f_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4213_){
_start:
{
uint8_t v_exe_boxed_4214_; lean_object* v_res_4215_; 
v_exe_boxed_4214_ = lean_unbox(v_exe_4213_);
v_res_4215_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4216_, lean_object* v_ext_4217_, uint8_t v_text_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v___x_4222_; 
lean_inc_ref(v_path_4216_);
v___x_4222_ = l_Lake_fetchFileHash___redArg(v_path_4216_, v_text_4218_, v_a_4219_, v_a_4220_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4241_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_a_4224_ = lean_ctor_get(v___x_4222_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4226_ = v___x_4222_;
v_isShared_4227_ = v_isSharedCheck_4241_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4241_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___x_4237_; 
v___x_4237_ = lean_io_metadata(v_path_4216_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v_modified_4239_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v_modified_4239_ = lean_ctor_get(v_a_4238_, 1);
lean_inc_ref(v_modified_4239_);
lean_dec(v_a_4238_);
v___y_4229_ = v_a_4224_;
v___y_4230_ = v_modified_4239_;
goto v___jp_4228_;
}
else
{
lean_object* v___x_4240_; 
lean_dec_ref_known(v___x_4237_, 1);
v___x_4240_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4229_ = v_a_4224_;
v___y_4230_ = v___x_4240_;
goto v___jp_4228_;
}
v___jp_4228_:
{
lean_object* v___x_4231_; uint64_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4231_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4231_, 0, v_ext_4217_);
v___x_4232_ = lean_unbox_uint64(v_a_4223_);
lean_dec(v_a_4223_);
lean_ctor_set_uint64(v___x_4231_, sizeof(void*)*1, v___x_4232_);
lean_inc_ref(v_path_4216_);
v___x_4233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4231_);
lean_ctor_set(v___x_4233_, 1, v_path_4216_);
lean_ctor_set(v___x_4233_, 2, v_path_4216_);
lean_ctor_set(v___x_4233_, 3, v___y_4230_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 1, v___y_4229_);
lean_ctor_set(v___x_4226_, 0, v___x_4233_);
v___x_4235_ = v___x_4226_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___y_4229_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_ext_4217_);
lean_dec_ref(v_path_4216_);
v_a_4242_ = lean_ctor_get(v___x_4222_, 0);
v_a_4243_ = lean_ctor_get(v___x_4222_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4222_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_inc(v_a_4242_);
lean_dec(v___x_4222_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4242_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4251_, lean_object* v_ext_4252_, lean_object* v_text_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
uint8_t v_text_boxed_4257_; lean_object* v_res_4258_; 
v_text_boxed_4257_ = lean_unbox(v_text_4253_);
v_res_4258_ = l_Lake_computeArtifact___redArg(v_path_4251_, v_ext_4252_, v_text_boxed_4257_, v_a_4254_, v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4259_, lean_object* v_ext_4260_, uint8_t v_text_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lake_computeArtifact___redArg(v_path_4259_, v_ext_4260_, v_text_4261_, v_a_4266_, v_a_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4270_, lean_object* v_ext_4271_, lean_object* v_text_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
uint8_t v_text_boxed_4280_; lean_object* v_res_4281_; 
v_text_boxed_4280_ = lean_unbox(v_text_4272_);
v_res_4281_ = l_Lake_computeArtifact(v_path_4270_, v_ext_4271_, v_text_boxed_4280_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4285_, lean_object* v_art_4286_, uint8_t v_exe_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___y_4291_; uint8_t v___x_4304_; 
v___x_4304_ = l_System_FilePath_pathExists(v_file_4285_);
if (v___x_4304_ == 0)
{
lean_object* v_descr_4305_; lean_object* v_path_4306_; lean_object* v___y_4308_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v_descr_4305_ = lean_ctor_get(v_art_4286_, 0);
v_path_4306_ = lean_ctor_get(v_art_4286_, 1);
v___x_4323_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4324_ = lean_string_append(v___x_4323_, v_path_4306_);
v___x_4325_ = 0;
v___x_4326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4326_, 0, v___x_4324_);
lean_ctor_set_uint8(v___x_4326_, sizeof(void*)*1, v___x_4325_);
v___x_4327_ = lean_array_push(v_a_4288_, v___x_4326_);
lean_inc_ref(v_file_4285_);
v___x_4328_ = l_Lake_createParentDirs(v_file_4285_);
if (lean_obj_tag(v___x_4328_) == 0)
{
uint8_t v___x_4329_; lean_object* v___x_4330_; 
lean_dec_ref_known(v___x_4328_, 1);
v___x_4329_ = 1;
v___x_4330_ = lean_io_hard_link(v_path_4306_, v_file_4285_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_dec_ref_known(v___x_4330_, 1);
if (v_exe_4287_ == 0)
{
v___y_4308_ = v___x_4327_;
goto v___jp_4307_;
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4331_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4331_, 0, v___x_4329_);
lean_ctor_set_uint8(v___x_4331_, 1, v___x_4304_);
lean_ctor_set_uint8(v___x_4331_, 2, v_exe_4287_);
lean_inc_ref_n(v___x_4331_, 2);
v___x_4332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
lean_ctor_set(v___x_4332_, 2, v___x_4331_);
v___x_4333_ = l_IO_setAccessRights(v_file_4285_, v___x_4332_);
lean_dec_ref_known(v___x_4332_, 3);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_dec_ref_known(v___x_4333_, 1);
v___y_4308_ = v___x_4327_;
goto v___jp_4307_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_dec_ref(v_art_4286_);
lean_dec_ref(v_file_4285_);
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = lean_io_error_to_string(v_a_4334_);
v___x_4336_ = 3;
v___x_4337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set_uint8(v___x_4337_, sizeof(void*)*1, v___x_4336_);
v___x_4338_ = lean_array_get_size(v___x_4327_);
v___x_4339_ = lean_array_push(v___x_4327_, v___x_4337_);
v___x_4340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
return v___x_4340_;
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_a_4341_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4342_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4343_ = lean_io_error_to_string(v_a_4341_);
v___x_4344_ = lean_string_append(v___x_4342_, v___x_4343_);
lean_dec_ref(v___x_4343_);
v___x_4345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*1, v___x_4325_);
v___x_4346_ = lean_array_push(v___x_4327_, v___x_4345_);
v___x_4347_ = l_Lake_copyFile(v_path_4306_, v_file_4285_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
lean_dec_ref_known(v___x_4347_, 1);
v___x_4348_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4348_, 0, v___x_4329_);
lean_ctor_set_uint8(v___x_4348_, 1, v___x_4304_);
lean_ctor_set_uint8(v___x_4348_, 2, v_exe_4287_);
lean_inc_ref_n(v___x_4348_, 2);
v___x_4349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4348_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
lean_ctor_set(v___x_4349_, 2, v___x_4348_);
v___x_4350_ = l_IO_setAccessRights(v_file_4285_, v___x_4349_);
lean_dec_ref_known(v___x_4349_, 3);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_dec_ref_known(v___x_4350_, 1);
v___y_4308_ = v___x_4346_;
goto v___jp_4307_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_dec_ref(v_art_4286_);
lean_dec_ref(v_file_4285_);
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = lean_io_error_to_string(v_a_4351_);
v___x_4353_ = 3;
v___x_4354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4354_, 0, v___x_4352_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*1, v___x_4353_);
v___x_4355_ = lean_array_get_size(v___x_4346_);
v___x_4356_ = lean_array_push(v___x_4346_, v___x_4354_);
v___x_4357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4355_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
return v___x_4357_;
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
lean_dec_ref(v_art_4286_);
lean_dec_ref(v_file_4285_);
v_a_4358_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4359_ = lean_io_error_to_string(v_a_4358_);
v___x_4360_ = 3;
v___x_4361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4361_, 0, v___x_4359_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*1, v___x_4360_);
v___x_4362_ = lean_array_get_size(v___x_4346_);
v___x_4363_ = lean_array_push(v___x_4346_, v___x_4361_);
v___x_4364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
return v___x_4364_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
lean_dec_ref(v_art_4286_);
lean_dec_ref(v_file_4285_);
v_a_4365_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4366_ = lean_io_error_to_string(v_a_4365_);
v___x_4367_ = 3;
v___x_4368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set_uint8(v___x_4368_, sizeof(void*)*1, v___x_4367_);
v___x_4369_ = lean_array_get_size(v___x_4327_);
v___x_4370_ = lean_array_push(v___x_4327_, v___x_4368_);
v___x_4371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4369_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
return v___x_4371_;
}
v___jp_4307_:
{
uint64_t v_hash_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v_hash_4309_ = lean_ctor_get_uint64(v_descr_4305_, sizeof(void*)*1);
v___x_4310_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4311_ = lean_string_append(v___x_4310_, v_file_4285_);
v___x_4312_ = 0;
v___x_4313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set_uint8(v___x_4313_, sizeof(void*)*1, v___x_4312_);
v___x_4314_ = lean_array_push(v___y_4308_, v___x_4313_);
lean_inc_ref(v_file_4285_);
v___x_4315_ = l_Lake_writeFileHash(v_file_4285_, v_hash_4309_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_dec_ref_known(v___x_4315_, 1);
v___y_4291_ = v___x_4314_;
goto v___jp_4290_;
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
lean_dec_ref(v_art_4286_);
lean_dec_ref(v_file_4285_);
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = lean_io_error_to_string(v_a_4316_);
v___x_4318_ = 3;
v___x_4319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set_uint8(v___x_4319_, sizeof(void*)*1, v___x_4318_);
v___x_4320_ = lean_array_get_size(v___x_4314_);
v___x_4321_ = lean_array_push(v___x_4314_, v___x_4319_);
v___x_4322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4320_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
return v___x_4322_;
}
}
}
else
{
v___y_4291_ = v_a_4288_;
goto v___jp_4290_;
}
v___jp_4290_:
{
lean_object* v_descr_4292_; lean_object* v_mtime_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4301_; 
v_descr_4292_ = lean_ctor_get(v_art_4286_, 0);
v_mtime_4293_ = lean_ctor_get(v_art_4286_, 3);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_art_4286_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; lean_object* v_unused_4303_; 
v_unused_4302_ = lean_ctor_get(v_art_4286_, 2);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_art_4286_, 1);
lean_dec(v_unused_4303_);
v___x_4295_ = v_art_4286_;
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_mtime_4293_);
lean_inc(v_descr_4292_);
lean_dec(v_art_4286_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
lean_inc_ref(v_file_4285_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 2, v_file_4285_);
lean_ctor_set(v___x_4295_, 1, v_file_4285_);
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_descr_4292_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_file_4285_);
lean_ctor_set(v_reuseFailAlloc_4300_, 2, v_file_4285_);
lean_ctor_set(v_reuseFailAlloc_4300_, 3, v_mtime_4293_);
v___x_4298_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set(v___x_4299_, 1, v___y_4291_);
return v___x_4299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4372_, lean_object* v_art_4373_, lean_object* v_exe_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
uint8_t v_exe_boxed_4377_; lean_object* v_res_4378_; 
v_exe_boxed_4377_ = lean_unbox(v_exe_4374_);
v_res_4378_ = l_Lake_restoreArtifact(v_file_4372_, v_art_4373_, v_exe_boxed_4377_, v_a_4375_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4379_, lean_object* v_a_x3f_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v_log_4384_; uint8_t v_action_4385_; uint8_t v_wantsRebuild_4386_; lean_object* v_trace_4387_; lean_object* v_buildTime_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4399_; 
v___x_4383_ = lean_io_mono_ms_now();
v_log_4384_ = lean_ctor_get(v___y_4381_, 0);
v_action_4385_ = lean_ctor_get_uint8(v___y_4381_, sizeof(void*)*3);
v_wantsRebuild_4386_ = lean_ctor_get_uint8(v___y_4381_, sizeof(void*)*3 + 1);
v_trace_4387_ = lean_ctor_get(v___y_4381_, 1);
v_buildTime_4388_ = lean_ctor_get(v___y_4381_, 2);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___y_4381_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4390_ = v___y_4381_;
v_isShared_4391_ = v_isSharedCheck_4399_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_buildTime_4388_);
lean_inc(v_trace_4387_);
lean_inc(v_log_4384_);
lean_dec(v___y_4381_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4399_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4392_ = lean_nat_sub(v___x_4383_, v_val_4379_);
lean_dec(v___x_4383_);
v___x_4393_ = lean_box(0);
v___x_4394_ = lean_nat_add(v_buildTime_4388_, v___x_4392_);
lean_dec(v___x_4392_);
lean_dec(v_buildTime_4388_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 2, v___x_4394_);
v___x_4396_ = v___x_4390_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_log_4384_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_trace_4387_);
lean_ctor_set(v_reuseFailAlloc_4398_, 2, v___x_4394_);
lean_ctor_set_uint8(v_reuseFailAlloc_4398_, sizeof(void*)*3, v_action_4385_);
lean_ctor_set_uint8(v_reuseFailAlloc_4398_, sizeof(void*)*3 + 1, v_wantsRebuild_4386_);
v___x_4396_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4393_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
return v___x_4397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4400_, lean_object* v_a_x3f_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4400_, v_a_x3f_4401_, v___y_4402_);
lean_dec(v_a_x3f_4401_);
lean_dec(v_val_4400_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4405_, lean_object* v_build_4406_, lean_object* v_traceFile_4407_, lean_object* v_ext_4408_, uint8_t v_text_4409_, lean_object* v_a_4410_, lean_object* v_depTrace_4411_, lean_object* v_traceFile_4412_, uint8_t v_action_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v_a_4421_; lean_object* v_a_4422_; lean_object* v_log_4425_; uint8_t v_action_4426_; uint8_t v_wantsRebuild_4427_; lean_object* v_trace_4428_; lean_object* v_buildTime_4429_; lean_object* v_toBuildConfig_4435_; lean_object* v_log_4436_; uint8_t v_action_4437_; uint8_t v_wantsRebuild_4438_; lean_object* v_trace_4439_; lean_object* v_buildTime_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4619_; 
v_toBuildConfig_4435_ = lean_ctor_get(v_a_4417_, 0);
v_log_4436_ = lean_ctor_get(v_a_4418_, 0);
v_action_4437_ = lean_ctor_get_uint8(v_a_4418_, sizeof(void*)*3);
v_wantsRebuild_4438_ = lean_ctor_get_uint8(v_a_4418_, sizeof(void*)*3 + 1);
v_trace_4439_ = lean_ctor_get(v_a_4418_, 1);
v_buildTime_4440_ = lean_ctor_get(v_a_4418_, 2);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_a_4418_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4442_ = v_a_4418_;
v_isShared_4443_ = v_isSharedCheck_4619_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_buildTime_4440_);
lean_inc(v_trace_4439_);
lean_inc(v_log_4436_);
lean_dec(v_a_4418_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4619_;
goto v_resetjp_4441_;
}
v___jp_4420_:
{
lean_object* v___x_4423_; 
v___x_4423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4423_, 0, v_a_4421_);
lean_ctor_set(v___x_4423_, 1, v_a_4422_);
return v___x_4423_;
}
v___jp_4424_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4430_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4431_ = lean_array_get_size(v_log_4425_);
v___x_4432_ = lean_array_push(v_log_4425_, v___x_4430_);
v___x_4433_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
lean_ctor_set(v___x_4433_, 1, v_trace_4428_);
lean_ctor_set(v___x_4433_, 2, v_buildTime_4429_);
lean_ctor_set_uint8(v___x_4433_, sizeof(void*)*3, v_action_4426_);
lean_ctor_set_uint8(v___x_4433_, sizeof(void*)*3 + 1, v_wantsRebuild_4427_);
v___x_4434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4431_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
return v___x_4434_;
}
v_resetjp_4441_:
{
uint8_t v_noBuild_4444_; uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v_noBuild_4444_ = lean_ctor_get_uint8(v_toBuildConfig_4435_, sizeof(void*)*4 + 2);
v___x_4445_ = l_Lake_JobAction_merge(v_action_4437_, v_action_4413_);
v___x_4446_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4412_);
v___x_4447_ = l_System_FilePath_addExtension(v_traceFile_4412_, v___x_4446_);
if (v_noBuild_4444_ == 0)
{
lean_object* v___x_4448_; lean_object* v_a_4450_; lean_object* v_a_4451_; lean_object* v___x_4455_; 
v___x_4448_ = lean_io_mono_ms_now();
v___x_4455_ = l_Lake_removeFileIfExists(v_file_4405_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4457_; 
lean_dec_ref_known(v___x_4455_, 1);
lean_inc_ref(v_log_4436_);
if (v_isShared_4443_ == 0)
{
v___x_4457_ = v___x_4442_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_log_4436_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_trace_4439_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_buildTime_4440_);
lean_ctor_set_uint8(v_reuseFailAlloc_4594_, sizeof(void*)*3 + 1, v_wantsRebuild_4438_);
v___x_4457_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4458_; 
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*3, v___x_4445_);
lean_inc_ref(v_a_4417_);
lean_inc(v_a_4416_);
lean_inc(v_a_4415_);
lean_inc(v_a_4414_);
v___x_4458_ = lean_apply_7(v_build_4406_, v_a_4410_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v___x_4457_, lean_box(0));
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v_log_4460_; uint8_t v_action_4461_; uint8_t v_wantsRebuild_4462_; lean_object* v_trace_4463_; lean_object* v_buildTime_4464_; lean_object* v___x_4465_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 1);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 2);
v_log_4460_ = lean_ctor_get(v_a_4459_, 0);
v_action_4461_ = lean_ctor_get_uint8(v_a_4459_, sizeof(void*)*3);
v_wantsRebuild_4462_ = lean_ctor_get_uint8(v_a_4459_, sizeof(void*)*3 + 1);
v_trace_4463_ = lean_ctor_get(v_a_4459_, 1);
v_buildTime_4464_ = lean_ctor_get(v_a_4459_, 2);
lean_inc_ref(v_file_4405_);
v___x_4465_ = l_Lake_clearFileHash(v_file_4405_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v___x_4466_; 
lean_dec_ref_known(v___x_4465_, 1);
v___x_4466_ = l_Lake_removeFileIfExists(v_traceFile_4407_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4558_; 
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v___x_4466_, 0);
lean_dec(v_unused_4559_);
v___x_4468_ = v___x_4466_;
v_isShared_4469_ = v_isSharedCheck_4558_;
goto v_resetjp_4467_;
}
else
{
lean_dec(v___x_4466_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4558_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_Lake_computeArtifact___redArg(v_file_4405_, v_ext_4408_, v_text_4409_, v_a_4417_, v_a_4459_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v_a_4472_; lean_object* v_descr_4473_; lean_object* v_log_4474_; uint8_t v_action_4475_; uint8_t v_wantsRebuild_4476_; lean_object* v_trace_4477_; lean_object* v_buildTime_4478_; uint64_t v_hash_4479_; lean_object* v_ext_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___y_4485_; lean_object* v___x_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 1);
lean_inc(v_a_4471_);
v_a_4472_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4470_, 2);
v_descr_4473_ = lean_ctor_get(v_a_4472_, 0);
v_log_4474_ = lean_ctor_get(v_a_4471_, 0);
v_action_4475_ = lean_ctor_get_uint8(v_a_4471_, sizeof(void*)*3);
v_wantsRebuild_4476_ = lean_ctor_get_uint8(v_a_4471_, sizeof(void*)*3 + 1);
v_trace_4477_ = lean_ctor_get(v_a_4471_, 1);
v_buildTime_4478_ = lean_ctor_get(v_a_4471_, 2);
v_hash_4479_ = lean_ctor_get_uint64(v_descr_4473_, sizeof(void*)*1);
v_ext_4480_ = lean_ctor_get(v_descr_4473_, 0);
v___x_4481_ = lean_array_get_size(v_log_4436_);
lean_dec_ref(v_log_4436_);
v___x_4482_ = lean_array_get_size(v_log_4474_);
v___x_4483_ = l_Array_extract___redArg(v_log_4474_, v___x_4481_, v___x_4482_);
v___x_4548_ = lean_string_utf8_byte_size(v_ext_4480_);
v___x_4549_ = lean_unsigned_to_nat(0u);
v___x_4550_ = lean_nat_dec_eq(v___x_4548_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4551_ = l_Lake_lowerHexUInt64(v_hash_4479_);
v___x_4552_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4553_ = lean_string_append(v___x_4551_, v___x_4552_);
v___x_4554_ = lean_string_append(v___x_4553_, v_ext_4480_);
v___y_4485_ = v___x_4554_;
goto v___jp_4484_;
}
else
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lake_lowerHexUInt64(v_hash_4479_);
v___y_4485_ = v___x_4555_;
goto v___jp_4484_;
}
v___jp_4484_:
{
lean_object* v___x_4487_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set_tag(v___x_4468_, 3);
lean_ctor_set(v___x_4468_, 0, v___y_4485_);
v___x_4487_ = v___x_4468_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___y_4485_);
v___x_4487_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4411_, v___x_4487_, v___x_4483_);
v___x_4489_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4412_, v___x_4488_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4530_; 
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4530_ == 0)
{
lean_object* v_unused_4531_; 
v_unused_4531_ = lean_ctor_get(v___x_4489_, 0);
lean_dec(v_unused_4531_);
v___x_4491_ = v___x_4489_;
v_isShared_4492_ = v_isSharedCheck_4530_;
goto v_resetjp_4490_;
}
else
{
lean_dec(v___x_4489_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4530_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Lake_removeFileIfExists(v___x_4447_);
lean_dec_ref(v___x_4447_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4513_; 
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; 
v_unused_4514_ = lean_ctor_get(v___x_4493_, 0);
lean_dec(v_unused_4514_);
v___x_4495_ = v___x_4493_;
v_isShared_4496_ = v_isSharedCheck_4513_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v___x_4493_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4513_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
lean_inc(v_a_4472_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v_a_4472_);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4472_);
v___x_4498_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4500_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set_tag(v___x_4491_, 1);
lean_ctor_set(v___x_4491_, 0, v___x_4498_);
v___x_4500_ = v___x_4491_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v___x_4501_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4448_, v___x_4500_, v_a_4471_);
lean_dec_ref(v___x_4500_);
lean_dec(v___x_4448_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 1);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4509_ == 0)
{
lean_object* v_unused_4510_; 
v_unused_4510_ = lean_ctor_get(v___x_4501_, 0);
lean_dec(v_unused_4510_);
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v_a_4472_);
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4472_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
}
else
{
lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4526_; 
lean_inc(v_buildTime_4478_);
lean_inc_ref(v_trace_4477_);
lean_inc_ref(v_log_4474_);
lean_del_object(v___x_4491_);
lean_dec(v_a_4472_);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_a_4471_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; lean_object* v_unused_4528_; lean_object* v_unused_4529_; 
v_unused_4527_ = lean_ctor_get(v_a_4471_, 2);
lean_dec(v_unused_4527_);
v_unused_4528_ = lean_ctor_get(v_a_4471_, 1);
lean_dec(v_unused_4528_);
v_unused_4529_ = lean_ctor_get(v_a_4471_, 0);
lean_dec(v_unused_4529_);
v___x_4516_ = v_a_4471_;
v_isShared_4517_ = v_isSharedCheck_4526_;
goto v_resetjp_4515_;
}
else
{
lean_dec(v_a_4471_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4526_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v_a_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4524_; 
v_a_4518_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4493_, 1);
v___x_4519_ = lean_io_error_to_string(v_a_4518_);
v___x_4520_ = 3;
v___x_4521_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set_uint8(v___x_4521_, sizeof(void*)*1, v___x_4520_);
v___x_4522_ = lean_array_push(v_log_4474_, v___x_4521_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4522_);
v___x_4524_ = v___x_4516_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_trace_4477_);
lean_ctor_set(v_reuseFailAlloc_4525_, 2, v_buildTime_4478_);
lean_ctor_set_uint8(v_reuseFailAlloc_4525_, sizeof(void*)*3, v_action_4475_);
lean_ctor_set_uint8(v_reuseFailAlloc_4525_, sizeof(void*)*3 + 1, v_wantsRebuild_4476_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
v_a_4450_ = v___x_4482_;
v_a_4451_ = v___x_4524_;
goto v___jp_4449_;
}
}
}
}
}
else
{
lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4543_; 
lean_inc(v_buildTime_4478_);
lean_inc_ref(v_trace_4477_);
lean_inc_ref(v_log_4474_);
lean_dec(v_a_4472_);
lean_dec_ref(v___x_4447_);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_a_4471_);
if (v_isSharedCheck_4543_ == 0)
{
lean_object* v_unused_4544_; lean_object* v_unused_4545_; lean_object* v_unused_4546_; 
v_unused_4544_ = lean_ctor_get(v_a_4471_, 2);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_a_4471_, 1);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_a_4471_, 0);
lean_dec(v_unused_4546_);
v___x_4533_ = v_a_4471_;
v_isShared_4534_ = v_isSharedCheck_4543_;
goto v_resetjp_4532_;
}
else
{
lean_dec(v_a_4471_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4543_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v_a_4535_; lean_object* v___x_4536_; uint8_t v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v_a_4535_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4536_ = lean_io_error_to_string(v_a_4535_);
v___x_4537_ = 3;
v___x_4538_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4538_, 0, v___x_4536_);
lean_ctor_set_uint8(v___x_4538_, sizeof(void*)*1, v___x_4537_);
v___x_4539_ = lean_array_push(v_log_4474_, v___x_4538_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v___x_4539_);
v___x_4541_ = v___x_4533_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_trace_4477_);
lean_ctor_set(v_reuseFailAlloc_4542_, 2, v_buildTime_4478_);
lean_ctor_set_uint8(v_reuseFailAlloc_4542_, sizeof(void*)*3, v_action_4475_);
lean_ctor_set_uint8(v_reuseFailAlloc_4542_, sizeof(void*)*3 + 1, v_wantsRebuild_4476_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
v_a_4450_ = v___x_4482_;
v_a_4451_ = v___x_4541_;
goto v___jp_4449_;
}
}
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v_a_4557_; 
lean_del_object(v___x_4468_);
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_log_4436_);
lean_dec_ref(v_traceFile_4412_);
v_a_4556_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4556_);
v_a_4557_ = lean_ctor_get(v___x_4470_, 1);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4470_, 2);
v_a_4450_ = v_a_4556_;
v_a_4451_ = v_a_4557_;
goto v___jp_4449_;
}
}
}
else
{
lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4572_; 
lean_inc(v_buildTime_4464_);
lean_inc_ref(v_trace_4463_);
lean_inc_ref(v_log_4460_);
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_log_4436_);
lean_dec_ref(v_traceFile_4412_);
lean_dec_ref(v_ext_4408_);
lean_dec_ref(v_file_4405_);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_a_4459_);
if (v_isSharedCheck_4572_ == 0)
{
lean_object* v_unused_4573_; lean_object* v_unused_4574_; lean_object* v_unused_4575_; 
v_unused_4573_ = lean_ctor_get(v_a_4459_, 2);
lean_dec(v_unused_4573_);
v_unused_4574_ = lean_ctor_get(v_a_4459_, 1);
lean_dec(v_unused_4574_);
v_unused_4575_ = lean_ctor_get(v_a_4459_, 0);
lean_dec(v_unused_4575_);
v___x_4561_ = v_a_4459_;
v_isShared_4562_ = v_isSharedCheck_4572_;
goto v_resetjp_4560_;
}
else
{
lean_dec(v_a_4459_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4572_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v_a_4563_; lean_object* v___x_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4570_; 
v_a_4563_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4466_, 1);
v___x_4564_ = lean_io_error_to_string(v_a_4563_);
v___x_4565_ = 3;
v___x_4566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4566_, 0, v___x_4564_);
lean_ctor_set_uint8(v___x_4566_, sizeof(void*)*1, v___x_4565_);
v___x_4567_ = lean_array_get_size(v_log_4460_);
v___x_4568_ = lean_array_push(v_log_4460_, v___x_4566_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4568_);
v___x_4570_ = v___x_4561_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_trace_4463_);
lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_buildTime_4464_);
lean_ctor_set_uint8(v_reuseFailAlloc_4571_, sizeof(void*)*3, v_action_4461_);
lean_ctor_set_uint8(v_reuseFailAlloc_4571_, sizeof(void*)*3 + 1, v_wantsRebuild_4462_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
v_a_4450_ = v___x_4567_;
v_a_4451_ = v___x_4570_;
goto v___jp_4449_;
}
}
}
}
else
{
lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4588_; 
lean_inc(v_buildTime_4464_);
lean_inc_ref(v_trace_4463_);
lean_inc_ref(v_log_4460_);
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_log_4436_);
lean_dec_ref(v_traceFile_4412_);
lean_dec_ref(v_ext_4408_);
lean_dec_ref(v_file_4405_);
v_isSharedCheck_4588_ = !lean_is_exclusive(v_a_4459_);
if (v_isSharedCheck_4588_ == 0)
{
lean_object* v_unused_4589_; lean_object* v_unused_4590_; lean_object* v_unused_4591_; 
v_unused_4589_ = lean_ctor_get(v_a_4459_, 2);
lean_dec(v_unused_4589_);
v_unused_4590_ = lean_ctor_get(v_a_4459_, 1);
lean_dec(v_unused_4590_);
v_unused_4591_ = lean_ctor_get(v_a_4459_, 0);
lean_dec(v_unused_4591_);
v___x_4577_ = v_a_4459_;
v_isShared_4578_ = v_isSharedCheck_4588_;
goto v_resetjp_4576_;
}
else
{
lean_dec(v_a_4459_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4588_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v_a_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4586_; 
v_a_4579_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4580_ = lean_io_error_to_string(v_a_4579_);
v___x_4581_ = 3;
v___x_4582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4582_, 0, v___x_4580_);
lean_ctor_set_uint8(v___x_4582_, sizeof(void*)*1, v___x_4581_);
v___x_4583_ = lean_array_get_size(v_log_4460_);
v___x_4584_ = lean_array_push(v_log_4460_, v___x_4582_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4584_);
v___x_4586_ = v___x_4577_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_trace_4463_);
lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_buildTime_4464_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*3, v_action_4461_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*3 + 1, v_wantsRebuild_4462_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
v_a_4450_ = v___x_4583_;
v_a_4451_ = v___x_4586_;
goto v___jp_4449_;
}
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v_a_4593_; 
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_log_4436_);
lean_dec_ref(v_traceFile_4412_);
lean_dec_ref(v_ext_4408_);
lean_dec_ref(v_file_4405_);
v_a_4592_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4592_);
v_a_4593_ = lean_ctor_get(v___x_4458_, 1);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4458_, 2);
v_a_4450_ = v_a_4592_;
v_a_4451_ = v_a_4593_;
goto v___jp_4449_;
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4596_; uint8_t v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_traceFile_4412_);
lean_dec_ref(v_a_4410_);
lean_dec_ref(v_ext_4408_);
lean_dec_ref(v_build_4406_);
lean_dec_ref(v_file_4405_);
v_a_4595_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4596_ = lean_io_error_to_string(v_a_4595_);
v___x_4597_ = 3;
v___x_4598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4598_, 0, v___x_4596_);
lean_ctor_set_uint8(v___x_4598_, sizeof(void*)*1, v___x_4597_);
v___x_4599_ = lean_array_get_size(v_log_4436_);
v___x_4600_ = lean_array_push(v_log_4436_, v___x_4598_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4600_);
v___x_4602_ = v___x_4442_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_trace_4439_);
lean_ctor_set(v_reuseFailAlloc_4603_, 2, v_buildTime_4440_);
lean_ctor_set_uint8(v_reuseFailAlloc_4603_, sizeof(void*)*3 + 1, v_wantsRebuild_4438_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_ctor_set_uint8(v___x_4602_, sizeof(void*)*3, v___x_4445_);
v_a_4450_ = v___x_4599_;
v_a_4451_ = v___x_4602_;
goto v___jp_4449_;
}
}
v___jp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v_a_4454_; 
v___x_4452_ = lean_box(0);
v___x_4453_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4448_, v___x_4452_, v_a_4451_);
lean_dec(v___x_4448_);
v_a_4454_ = lean_ctor_get(v___x_4453_, 1);
lean_inc(v_a_4454_);
lean_dec_ref(v___x_4453_);
v_a_4421_ = v_a_4450_;
v_a_4422_ = v_a_4454_;
goto v___jp_4420_;
}
}
else
{
uint8_t v___x_4604_; 
lean_dec_ref(v_a_4410_);
lean_dec_ref(v_ext_4408_);
lean_dec_ref(v_build_4406_);
lean_dec_ref(v_file_4405_);
v___x_4604_ = l_System_FilePath_pathExists(v_traceFile_4412_);
lean_dec_ref(v_traceFile_4412_);
if (v___x_4604_ == 0)
{
lean_dec_ref(v___x_4447_);
lean_del_object(v___x_4442_);
v_log_4425_ = v_log_4436_;
v_action_4426_ = v___x_4445_;
v_wantsRebuild_4427_ = v_noBuild_4444_;
v_trace_4428_ = v_trace_4439_;
v_buildTime_4429_ = v_buildTime_4440_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4605_ = lean_box(0);
v___x_4606_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4607_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4411_, v___x_4605_, v___x_4606_);
v___x_4608_ = l_Lake_BuildMetadata_writeFile(v___x_4447_, v___x_4607_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_dec_ref_known(v___x_4608_, 1);
lean_del_object(v___x_4442_);
v_log_4425_ = v_log_4436_;
v_action_4426_ = v___x_4445_;
v_wantsRebuild_4427_ = v_noBuild_4444_;
v_trace_4428_ = v_trace_4439_;
v_buildTime_4429_ = v_buildTime_4440_;
goto v___jp_4424_;
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4616_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
v___x_4610_ = lean_io_error_to_string(v_a_4609_);
v___x_4611_ = 3;
v___x_4612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4612_, 0, v___x_4610_);
lean_ctor_set_uint8(v___x_4612_, sizeof(void*)*1, v___x_4611_);
v___x_4613_ = lean_array_get_size(v_log_4436_);
v___x_4614_ = lean_array_push(v_log_4436_, v___x_4612_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4614_);
v___x_4616_ = v___x_4442_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v_trace_4439_);
lean_ctor_set(v_reuseFailAlloc_4618_, 2, v_buildTime_4440_);
v___x_4616_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
lean_object* v___x_4617_; 
lean_ctor_set_uint8(v___x_4616_, sizeof(void*)*3, v___x_4445_);
lean_ctor_set_uint8(v___x_4616_, sizeof(void*)*3 + 1, v_noBuild_4444_);
v___x_4617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4613_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
return v___x_4617_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4620_, lean_object* v_build_4621_, lean_object* v_traceFile_4622_, lean_object* v_ext_4623_, lean_object* v_text_4624_, lean_object* v_a_4625_, lean_object* v_depTrace_4626_, lean_object* v_traceFile_4627_, lean_object* v_action_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
uint8_t v_text_boxed_4635_; uint8_t v_action_boxed_4636_; lean_object* v_res_4637_; 
v_text_boxed_4635_ = lean_unbox(v_text_4624_);
v_action_boxed_4636_ = lean_unbox(v_action_4628_);
v_res_4637_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4620_, v_build_4621_, v_traceFile_4622_, v_ext_4623_, v_text_boxed_4635_, v_a_4625_, v_depTrace_4626_, v_traceFile_4627_, v_action_boxed_4636_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_depTrace_4626_);
lean_dec_ref(v_traceFile_4622_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4638_, lean_object* v_build_4639_, uint8_t v_text_4640_, lean_object* v_ext_4641_, lean_object* v_depTrace_4642_, lean_object* v_traceFile_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
uint8_t v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = 5;
lean_inc_ref(v_traceFile_4643_);
v___x_4652_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4638_, v_build_4639_, v_traceFile_4643_, v_ext_4641_, v_text_4640_, v_a_4644_, v_depTrace_4642_, v_traceFile_4643_, v___x_4651_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec_ref(v_traceFile_4643_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4653_, lean_object* v_build_4654_, lean_object* v_text_4655_, lean_object* v_ext_4656_, lean_object* v_depTrace_4657_, lean_object* v_traceFile_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
uint8_t v_text_boxed_4666_; lean_object* v_res_4667_; 
v_text_boxed_4666_ = lean_unbox(v_text_4655_);
v_res_4667_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4653_, v_build_4654_, v_text_boxed_4666_, v_ext_4656_, v_depTrace_4657_, v_traceFile_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_depTrace_4657_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4669_, lean_object* v_traceFile_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_log_4673_; uint8_t v_action_4674_; uint8_t v_wantsRebuild_4675_; lean_object* v_trace_4676_; lean_object* v_buildTime_4677_; lean_object* v___x_4678_; 
v_log_4673_ = lean_ctor_get(v_a_4671_, 0);
v_action_4674_ = lean_ctor_get_uint8(v_a_4671_, sizeof(void*)*3);
v_wantsRebuild_4675_ = lean_ctor_get_uint8(v_a_4671_, sizeof(void*)*3 + 1);
v_trace_4676_ = lean_ctor_get(v_a_4671_, 1);
v_buildTime_4677_ = lean_ctor_get(v_a_4671_, 2);
v___x_4678_ = lean_io_metadata(v_traceFile_4670_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v_modified_4680_; lean_object* v_descr_4681_; lean_object* v_path_4682_; lean_object* v_name_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4691_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v_modified_4680_ = lean_ctor_get(v_a_4679_, 1);
lean_inc_ref(v_modified_4680_);
lean_dec(v_a_4679_);
v_descr_4681_ = lean_ctor_get(v_art_4669_, 0);
v_path_4682_ = lean_ctor_get(v_art_4669_, 1);
v_name_4683_ = lean_ctor_get(v_art_4669_, 2);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_art_4669_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; 
v_unused_4692_ = lean_ctor_get(v_art_4669_, 3);
lean_dec(v_unused_4692_);
v___x_4685_ = v_art_4669_;
v_isShared_4686_ = v_isSharedCheck_4691_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_name_4683_);
lean_inc(v_path_4682_);
lean_inc(v_descr_4681_);
lean_dec(v_art_4669_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4691_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 3, v_modified_4680_);
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_descr_4681_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v_path_4682_);
lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_name_4683_);
lean_ctor_set(v_reuseFailAlloc_4690_, 3, v_modified_4680_);
v___x_4688_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v_a_4671_);
return v___x_4689_;
}
}
}
else
{
lean_object* v_a_4693_; 
v_a_4693_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___x_4678_, 1);
if (lean_obj_tag(v_a_4693_) == 11)
{
lean_object* v___x_4694_; 
lean_dec_ref_known(v_a_4693_, 2);
v___x_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4694_, 0, v_art_4669_);
lean_ctor_set(v___x_4694_, 1, v_a_4671_);
return v___x_4694_;
}
else
{
lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4709_; 
lean_inc(v_buildTime_4677_);
lean_inc_ref(v_trace_4676_);
lean_inc_ref(v_log_4673_);
lean_dec_ref(v_art_4669_);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_a_4671_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; lean_object* v_unused_4711_; lean_object* v_unused_4712_; 
v_unused_4710_ = lean_ctor_get(v_a_4671_, 2);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_a_4671_, 1);
lean_dec(v_unused_4711_);
v_unused_4712_ = lean_ctor_get(v_a_4671_, 0);
lean_dec(v_unused_4712_);
v___x_4696_ = v_a_4671_;
v_isShared_4697_ = v_isSharedCheck_4709_;
goto v_resetjp_4695_;
}
else
{
lean_dec(v_a_4671_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4709_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4698_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4699_ = lean_io_error_to_string(v_a_4693_);
v___x_4700_ = lean_string_append(v___x_4698_, v___x_4699_);
lean_dec_ref(v___x_4699_);
v___x_4701_ = 3;
v___x_4702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4702_, 0, v___x_4700_);
lean_ctor_set_uint8(v___x_4702_, sizeof(void*)*1, v___x_4701_);
v___x_4703_ = lean_array_get_size(v_log_4673_);
v___x_4704_ = lean_array_push(v_log_4673_, v___x_4702_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4704_);
v___x_4706_ = v___x_4696_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4704_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_trace_4676_);
lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_buildTime_4677_);
lean_ctor_set_uint8(v_reuseFailAlloc_4708_, sizeof(void*)*3, v_action_4674_);
lean_ctor_set_uint8(v_reuseFailAlloc_4708_, sizeof(void*)*3 + 1, v_wantsRebuild_4675_);
v___x_4706_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4703_);
lean_ctor_set(v___x_4707_, 1, v___x_4706_);
return v___x_4707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4713_, lean_object* v_traceFile_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4713_, v_traceFile_4714_, v_a_4715_);
lean_dec_ref(v_traceFile_4714_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4718_, lean_object* v_traceFile_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4718_, v_traceFile_4719_, v_a_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4728_, lean_object* v_traceFile_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4728_, v_traceFile_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec_ref(v_traceFile_4729_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4738_, lean_object* v_____r_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v___x_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4747_, 0, v_a_4738_);
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
v___x_4749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
lean_ctor_set(v___x_4749_, 1, v___y_4745_);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4750_, lean_object* v_____r_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4750_, v_____r_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4760_, lean_object* v___y_4761_, uint64_t v_inputHash_4762_, lean_object* v_savedTrace_4763_, lean_object* v_pkg_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___y_4772_; lean_object* v_a_4776_; lean_object* v_a_4777_; lean_object* v___y_4792_; 
if (lean_obj_tag(v_savedTrace_4763_) == 2)
{
lean_object* v_data_4807_; uint64_t v_depHash_4808_; lean_object* v_outputs_x3f_4809_; uint8_t v___x_4810_; 
v_data_4807_ = lean_ctor_get(v_savedTrace_4763_, 0);
lean_inc_ref(v_data_4807_);
lean_dec_ref_known(v_savedTrace_4763_, 1);
v_depHash_4808_ = lean_ctor_get_uint64(v_data_4807_, sizeof(void*)*3);
v_outputs_x3f_4809_ = lean_ctor_get(v_data_4807_, 1);
lean_inc(v_outputs_x3f_4809_);
lean_dec_ref(v_data_4807_);
v___x_4810_ = lean_uint64_dec_eq(v_depHash_4808_, v_inputHash_4762_);
if (v___x_4810_ == 0)
{
lean_dec(v_outputs_x3f_4809_);
lean_dec_ref(v_pkg_4764_);
lean_dec_ref(v___y_4761_);
v___y_4772_ = v_a_4769_;
goto v___jp_4771_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4809_) == 1)
{
lean_object* v_val_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_val_4811_ = lean_ctor_get(v_outputs_x3f_4809_, 0);
lean_inc_n(v_val_4811_, 2);
lean_dec_ref_known(v_outputs_x3f_4809_, 1);
v___x_4812_ = lean_box(0);
v___x_4813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4813_, 0, v_val_4811_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
lean_ctor_set(v___x_4813_, 2, v___x_4812_);
lean_inc_ref(v___y_4761_);
v___x_4814_ = l_Lake_resolveArtifactOutput(v___x_4813_, v_exe_4760_, v___y_4761_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_config_4815_; lean_object* v_a_4816_; lean_object* v_a_4817_; lean_object* v_enableArtifactCache_x3f_4818_; lean_object* v_a_4820_; uint8_t v_a_4824_; lean_object* v_a_4825_; 
v_config_4815_ = lean_ctor_get(v_pkg_4764_, 6);
v_a_4816_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4816_);
v_a_4817_ = lean_ctor_get(v___x_4814_, 1);
lean_inc(v_a_4817_);
lean_dec_ref_known(v___x_4814_, 2);
v_enableArtifactCache_x3f_4818_ = lean_ctor_get(v_config_4815_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4818_) == 0)
{
lean_object* v_toContext_4857_; lean_object* v_lakeEnv_4858_; lean_object* v_enableArtifactCache_x3f_4859_; 
v_toContext_4857_ = lean_ctor_get(v_a_4768_, 1);
v_lakeEnv_4858_ = lean_ctor_get(v_toContext_4857_, 0);
v_enableArtifactCache_x3f_4859_ = lean_ctor_get(v_lakeEnv_4858_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4859_) == 0)
{
lean_object* v_packages_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v_config_4863_; lean_object* v_enableArtifactCache_x3f_4864_; 
v_packages_4860_ = lean_ctor_get(v_toContext_4857_, 4);
v___x_4861_ = lean_unsigned_to_nat(0u);
v___x_4862_ = lean_array_fget_borrowed(v_packages_4860_, v___x_4861_);
v_config_4863_ = lean_ctor_get(v___x_4862_, 6);
v_enableArtifactCache_x3f_4864_ = lean_ctor_get(v_config_4863_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4864_) == 0)
{
lean_dec(v_val_4811_);
lean_dec_ref(v_pkg_4764_);
v_a_4820_ = v_a_4817_;
goto v___jp_4819_;
}
else
{
lean_object* v_val_4865_; uint8_t v___x_4866_; 
v_val_4865_ = lean_ctor_get(v_enableArtifactCache_x3f_4864_, 0);
v___x_4866_ = lean_unbox(v_val_4865_);
v_a_4824_ = v___x_4866_;
v_a_4825_ = v_a_4817_;
goto v___jp_4823_;
}
}
else
{
lean_object* v_val_4867_; uint8_t v___x_4868_; 
v_val_4867_ = lean_ctor_get(v_enableArtifactCache_x3f_4859_, 0);
v___x_4868_ = lean_unbox(v_val_4867_);
v_a_4824_ = v___x_4868_;
v_a_4825_ = v_a_4817_;
goto v___jp_4823_;
}
}
else
{
lean_object* v_val_4869_; uint8_t v___x_4870_; 
v_val_4869_ = lean_ctor_get(v_enableArtifactCache_x3f_4818_, 0);
v___x_4870_ = lean_unbox(v_val_4869_);
v_a_4824_ = v___x_4870_;
v_a_4825_ = v_a_4817_;
goto v___jp_4823_;
}
v___jp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4821_ = lean_box(0);
v___x_4822_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4816_, v___x_4821_, v___y_4761_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4820_);
lean_dec_ref(v___y_4761_);
v___y_4792_ = v___x_4822_;
goto v___jp_4791_;
}
v___jp_4823_:
{
if (v_a_4824_ == 0)
{
lean_dec(v_val_4811_);
lean_dec_ref(v_pkg_4764_);
v_a_4820_ = v_a_4825_;
goto v___jp_4819_;
}
else
{
lean_object* v_toContext_4826_; lean_object* v_log_4827_; uint8_t v_action_4828_; uint8_t v_wantsRebuild_4829_; lean_object* v_trace_4830_; lean_object* v_buildTime_4831_; lean_object* v_lakeCache_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; lean_object* v___x_4835_; 
v_toContext_4826_ = lean_ctor_get(v_a_4768_, 1);
v_log_4827_ = lean_ctor_get(v_a_4825_, 0);
v_action_4828_ = lean_ctor_get_uint8(v_a_4825_, sizeof(void*)*3);
v_wantsRebuild_4829_ = lean_ctor_get_uint8(v_a_4825_, sizeof(void*)*3 + 1);
v_trace_4830_ = lean_ctor_get(v_a_4825_, 1);
v_buildTime_4831_ = lean_ctor_get(v_a_4825_, 2);
v_lakeCache_4832_ = lean_ctor_get(v_toContext_4826_, 2);
v___x_4833_ = l_Lake_Package_cacheScope(v_pkg_4764_);
v___x_4834_ = 0;
lean_inc_ref(v_lakeCache_4832_);
v___x_4835_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4832_, v___x_4833_, v_inputHash_4762_, v_val_4811_, v___x_4812_, v___x_4812_, v___x_4834_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
lean_dec_ref_known(v___x_4835_, 1);
v___x_4836_ = lean_box(0);
v___x_4837_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4816_, v___x_4836_, v___y_4761_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4825_);
lean_dec_ref(v___y_4761_);
v___y_4792_ = v___x_4837_;
goto v___jp_4791_;
}
else
{
lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4853_; 
lean_inc(v_buildTime_4831_);
lean_inc_ref(v_trace_4830_);
lean_inc_ref(v_log_4827_);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_a_4825_);
if (v_isSharedCheck_4853_ == 0)
{
lean_object* v_unused_4854_; lean_object* v_unused_4855_; lean_object* v_unused_4856_; 
v_unused_4854_ = lean_ctor_get(v_a_4825_, 2);
lean_dec(v_unused_4854_);
v_unused_4855_ = lean_ctor_get(v_a_4825_, 1);
lean_dec(v_unused_4855_);
v_unused_4856_ = lean_ctor_get(v_a_4825_, 0);
lean_dec(v_unused_4856_);
v___x_4839_ = v_a_4825_;
v_isShared_4840_ = v_isSharedCheck_4853_;
goto v_resetjp_4838_;
}
else
{
lean_dec(v_a_4825_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4853_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v_a_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; uint8_t v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4850_; 
v_a_4841_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___x_4835_, 1);
v___x_4842_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4843_ = lean_io_error_to_string(v_a_4841_);
v___x_4844_ = lean_string_append(v___x_4842_, v___x_4843_);
lean_dec_ref(v___x_4843_);
v___x_4845_ = 2;
v___x_4846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4846_, 0, v___x_4844_);
lean_ctor_set_uint8(v___x_4846_, sizeof(void*)*1, v___x_4845_);
v___x_4847_ = lean_box(0);
v___x_4848_ = lean_array_push(v_log_4827_, v___x_4846_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 0, v___x_4848_);
v___x_4850_ = v___x_4839_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4848_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v_trace_4830_);
lean_ctor_set(v_reuseFailAlloc_4852_, 2, v_buildTime_4831_);
lean_ctor_set_uint8(v_reuseFailAlloc_4852_, sizeof(void*)*3, v_action_4828_);
lean_ctor_set_uint8(v_reuseFailAlloc_4852_, sizeof(void*)*3 + 1, v_wantsRebuild_4829_);
v___x_4850_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4816_, v___x_4847_, v___y_4761_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v___x_4850_);
lean_dec_ref(v___y_4761_);
v___y_4792_ = v___x_4851_;
goto v___jp_4791_;
}
}
}
}
}
}
else
{
lean_object* v_a_4871_; lean_object* v_a_4872_; 
lean_dec(v_val_4811_);
lean_dec_ref(v_pkg_4764_);
lean_dec_ref(v___y_4761_);
v_a_4871_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4871_);
v_a_4872_ = lean_ctor_get(v___x_4814_, 1);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4814_, 2);
v_a_4776_ = v_a_4871_;
v_a_4777_ = v_a_4872_;
goto v___jp_4775_;
}
}
else
{
lean_dec(v_outputs_x3f_4809_);
lean_dec_ref(v_pkg_4764_);
lean_dec_ref(v___y_4761_);
v___y_4772_ = v_a_4769_;
goto v___jp_4771_;
}
}
}
else
{
lean_dec_ref(v_pkg_4764_);
lean_dec(v_savedTrace_4763_);
lean_dec_ref(v___y_4761_);
v___y_4772_ = v_a_4769_;
goto v___jp_4771_;
}
v___jp_4771_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_box(0);
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
lean_ctor_set(v___x_4774_, 1, v___y_4772_);
return v___x_4774_;
}
v___jp_4775_:
{
lean_object* v_log_4778_; uint8_t v_action_4779_; uint8_t v_wantsRebuild_4780_; lean_object* v_trace_4781_; lean_object* v_buildTime_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4790_; 
v_log_4778_ = lean_ctor_get(v_a_4777_, 0);
v_action_4779_ = lean_ctor_get_uint8(v_a_4777_, sizeof(void*)*3);
v_wantsRebuild_4780_ = lean_ctor_get_uint8(v_a_4777_, sizeof(void*)*3 + 1);
v_trace_4781_ = lean_ctor_get(v_a_4777_, 1);
v_buildTime_4782_ = lean_ctor_get(v_a_4777_, 2);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_a_4777_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4784_ = v_a_4777_;
v_isShared_4785_ = v_isSharedCheck_4790_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_buildTime_4782_);
lean_inc(v_trace_4781_);
lean_inc(v_log_4778_);
lean_dec(v_a_4777_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4790_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4786_ = l_Array_shrink___redArg(v_log_4778_, v_a_4776_);
lean_dec(v_a_4776_);
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v___x_4786_);
v___x_4788_ = v___x_4784_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_trace_4781_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_buildTime_4782_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*3, v_action_4779_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*3 + 1, v_wantsRebuild_4780_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
v___y_4772_ = v___x_4788_;
goto v___jp_4771_;
}
}
}
v___jp_4791_:
{
if (lean_obj_tag(v___y_4792_) == 0)
{
lean_object* v_a_4793_; 
v_a_4793_ = lean_ctor_get(v___y_4792_, 0);
if (lean_obj_tag(v_a_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4802_; 
lean_inc_ref(v_a_4793_);
v_a_4794_ = lean_ctor_get(v___y_4792_, 1);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___y_4792_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; 
v_unused_4803_ = lean_ctor_get(v___y_4792_, 0);
lean_dec(v_unused_4803_);
v___x_4796_ = v___y_4792_;
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___y_4792_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v_a_4798_; lean_object* v___x_4800_; 
v_a_4798_ = lean_ctor_get(v_a_4793_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v_a_4793_, 1);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v_a_4798_);
v___x_4800_ = v___x_4796_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4798_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_a_4794_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
else
{
lean_object* v_a_4804_; 
v_a_4804_ = lean_ctor_get(v___y_4792_, 1);
lean_inc(v_a_4804_);
lean_dec_ref_known(v___y_4792_, 2);
v___y_4772_ = v_a_4804_;
goto v___jp_4771_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v_a_4806_; 
v_a_4805_ = lean_ctor_get(v___y_4792_, 0);
lean_inc(v_a_4805_);
v_a_4806_ = lean_ctor_get(v___y_4792_, 1);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___y_4792_, 2);
v_a_4776_ = v_a_4805_;
v_a_4777_ = v_a_4806_;
goto v___jp_4775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4873_, lean_object* v___y_4874_, lean_object* v_inputHash_4875_, lean_object* v_savedTrace_4876_, lean_object* v_pkg_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
uint8_t v_exe_boxed_4884_; uint64_t v_inputHash_boxed_4885_; lean_object* v_res_4886_; 
v_exe_boxed_4884_ = lean_unbox(v_exe_4873_);
v_inputHash_boxed_4885_ = lean_unbox_uint64(v_inputHash_4875_);
lean_dec_ref(v_inputHash_4875_);
v_res_4886_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4884_, v___y_4874_, v_inputHash_boxed_4885_, v_savedTrace_4876_, v_pkg_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec(v_a_4878_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4887_, size_t v_i_4888_, size_t v_stop_4889_, lean_object* v_b_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_eq(v_i_4888_, v_stop_4889_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; lean_object* v_message_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; size_t v___x_4897_; size_t v___x_4898_; 
v___x_4892_ = lean_array_uget_borrowed(v_as_4887_, v_i_4888_);
v_message_4893_ = lean_ctor_get(v___x_4892_, 0);
v___x_4894_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4895_ = lean_string_append(v_b_4890_, v___x_4894_);
v___x_4896_ = lean_string_append(v___x_4895_, v_message_4893_);
v___x_4897_ = ((size_t)1ULL);
v___x_4898_ = lean_usize_add(v_i_4888_, v___x_4897_);
v_i_4888_ = v___x_4898_;
v_b_4890_ = v___x_4896_;
goto _start;
}
else
{
return v_b_4890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4900_, lean_object* v_i_4901_, lean_object* v_stop_4902_, lean_object* v_b_4903_){
_start:
{
size_t v_i_boxed_4904_; size_t v_stop_boxed_4905_; lean_object* v_res_4906_; 
v_i_boxed_4904_ = lean_unbox_usize(v_i_4901_);
lean_dec(v_i_4901_);
v_stop_boxed_4905_ = lean_unbox_usize(v_stop_4902_);
lean_dec(v_stop_4902_);
v_res_4906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4900_, v_i_boxed_4904_, v_stop_boxed_4905_, v_b_4903_);
lean_dec_ref(v_as_4900_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4907_, lean_object* v___y_4908_, uint64_t v_inputHash_4909_, lean_object* v_pkg_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_r_4918_; lean_object* v___y_4919_; uint8_t v___y_4922_; lean_object* v___y_4923_; uint8_t v___y_4924_; lean_object* v___y_4925_; lean_object* v___y_4926_; lean_object* v___y_4927_; lean_object* v_a_4934_; lean_object* v_log_4935_; uint8_t v_action_4936_; uint8_t v_wantsRebuild_4937_; lean_object* v_trace_4938_; lean_object* v_buildTime_4939_; lean_object* v_toContext_4964_; lean_object* v_log_4965_; uint8_t v_action_4966_; uint8_t v_wantsRebuild_4967_; lean_object* v_trace_4968_; lean_object* v_buildTime_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_5002_; 
v_toContext_4964_ = lean_ctor_get(v_a_4914_, 1);
v_log_4965_ = lean_ctor_get(v_a_4915_, 0);
v_action_4966_ = lean_ctor_get_uint8(v_a_4915_, sizeof(void*)*3);
v_wantsRebuild_4967_ = lean_ctor_get_uint8(v_a_4915_, sizeof(void*)*3 + 1);
v_trace_4968_ = lean_ctor_get(v_a_4915_, 1);
v_buildTime_4969_ = lean_ctor_get(v_a_4915_, 2);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_a_4915_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4971_ = v_a_4915_;
v_isShared_4972_ = v_isSharedCheck_5002_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_buildTime_4969_);
lean_inc(v_trace_4968_);
lean_inc(v_log_4965_);
lean_dec(v_a_4915_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_5002_;
goto v_resetjp_4970_;
}
v___jp_4917_:
{
lean_object* v___x_4920_; 
v___x_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4920_, 0, v_r_4918_);
lean_ctor_set(v___x_4920_, 1, v___y_4919_);
return v___x_4920_;
}
v___jp_4921_:
{
uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4928_ = 0;
v___x_4929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4929_, 0, v___y_4927_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1, v___x_4928_);
v___x_4930_ = lean_array_push(v___y_4926_, v___x_4929_);
v___x_4931_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v___y_4925_);
lean_ctor_set(v___x_4931_, 2, v___y_4923_);
lean_ctor_set_uint8(v___x_4931_, sizeof(void*)*3, v___y_4924_);
lean_ctor_set_uint8(v___x_4931_, sizeof(void*)*3 + 1, v___y_4922_);
v___x_4932_ = lean_box(0);
v_r_4918_ = v___x_4932_;
v___y_4919_ = v___x_4931_;
goto v___jp_4917_;
}
v___jp_4933_:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; 
v___x_4940_ = lean_array_get_size(v_log_4935_);
lean_inc(v_a_4934_);
v___x_4941_ = l_Array_extract___redArg(v_log_4935_, v_a_4934_, v___x_4940_);
v___x_4942_ = l_Array_shrink___redArg(v_log_4935_, v_a_4934_);
lean_dec(v_a_4934_);
v___x_4943_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4944_ = l_Lake_lowerHexUInt64(v_inputHash_4909_);
v___x_4945_ = lean_unsigned_to_nat(7u);
v___x_4946_ = lean_unsigned_to_nat(0u);
v___x_4947_ = lean_string_utf8_byte_size(v___x_4944_);
lean_inc_ref(v___x_4944_);
v___x_4948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4944_);
lean_ctor_set(v___x_4948_, 1, v___x_4946_);
lean_ctor_set(v___x_4948_, 2, v___x_4947_);
v___x_4949_ = l_String_Slice_Pos_nextn(v___x_4948_, v___x_4946_, v___x_4945_);
lean_dec_ref_known(v___x_4948_, 3);
v___x_4950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4944_);
lean_ctor_set(v___x_4950_, 1, v___x_4946_);
lean_ctor_set(v___x_4950_, 2, v___x_4949_);
v___x_4951_ = l_String_Slice_toString(v___x_4950_);
lean_dec_ref_known(v___x_4950_, 3);
v___x_4952_ = lean_string_append(v___x_4943_, v___x_4951_);
lean_dec_ref(v___x_4951_);
v___x_4953_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_4954_ = lean_string_append(v___x_4952_, v___x_4953_);
v___x_4955_ = lean_array_get_size(v___x_4941_);
v___x_4956_ = lean_nat_dec_lt(v___x_4946_, v___x_4955_);
if (v___x_4956_ == 0)
{
lean_dec_ref(v___x_4941_);
v___y_4922_ = v_wantsRebuild_4937_;
v___y_4923_ = v_buildTime_4939_;
v___y_4924_ = v_action_4936_;
v___y_4925_ = v_trace_4938_;
v___y_4926_ = v___x_4942_;
v___y_4927_ = v___x_4954_;
goto v___jp_4921_;
}
else
{
uint8_t v___x_4957_; 
v___x_4957_ = lean_nat_dec_le(v___x_4955_, v___x_4955_);
if (v___x_4957_ == 0)
{
if (v___x_4956_ == 0)
{
lean_dec_ref(v___x_4941_);
v___y_4922_ = v_wantsRebuild_4937_;
v___y_4923_ = v_buildTime_4939_;
v___y_4924_ = v_action_4936_;
v___y_4925_ = v_trace_4938_;
v___y_4926_ = v___x_4942_;
v___y_4927_ = v___x_4954_;
goto v___jp_4921_;
}
else
{
size_t v___x_4958_; size_t v___x_4959_; lean_object* v___x_4960_; 
v___x_4958_ = ((size_t)0ULL);
v___x_4959_ = lean_usize_of_nat(v___x_4955_);
v___x_4960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4941_, v___x_4958_, v___x_4959_, v___x_4954_);
lean_dec_ref(v___x_4941_);
v___y_4922_ = v_wantsRebuild_4937_;
v___y_4923_ = v_buildTime_4939_;
v___y_4924_ = v_action_4936_;
v___y_4925_ = v_trace_4938_;
v___y_4926_ = v___x_4942_;
v___y_4927_ = v___x_4960_;
goto v___jp_4921_;
}
}
else
{
size_t v___x_4961_; size_t v___x_4962_; lean_object* v___x_4963_; 
v___x_4961_ = ((size_t)0ULL);
v___x_4962_ = lean_usize_of_nat(v___x_4955_);
v___x_4963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4941_, v___x_4961_, v___x_4962_, v___x_4954_);
lean_dec_ref(v___x_4941_);
v___y_4922_ = v_wantsRebuild_4937_;
v___y_4923_ = v_buildTime_4939_;
v___y_4924_ = v_action_4936_;
v___y_4925_ = v_trace_4938_;
v___y_4926_ = v___x_4942_;
v___y_4927_ = v___x_4963_;
goto v___jp_4921_;
}
}
}
v_resetjp_4970_:
{
lean_object* v_lakeCache_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v_lakeCache_4973_ = lean_ctor_get(v_toContext_4964_, 2);
v___x_4974_ = l_Lake_Package_cacheScope(v_pkg_4910_);
lean_inc_ref(v_lakeCache_4973_);
v___x_4975_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4973_, v___x_4974_, v_inputHash_4909_, v_log_4965_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v_a_4977_; lean_object* v___x_4979_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
v_a_4977_ = lean_ctor_get(v___x_4975_, 1);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4975_, 2);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 0, v_a_4977_);
v___x_4979_ = v___x_4971_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4977_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_trace_4968_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v_buildTime_4969_);
lean_ctor_set_uint8(v_reuseFailAlloc_4999_, sizeof(void*)*3, v_action_4966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4999_, sizeof(void*)*3 + 1, v_wantsRebuild_4967_);
v___x_4979_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
if (lean_obj_tag(v_a_4976_) == 0)
{
lean_object* v___x_4980_; 
lean_dec_ref(v___y_4908_);
v___x_4980_ = lean_box(0);
v_r_4918_ = v___x_4980_;
v___y_4919_ = v___x_4979_;
goto v___jp_4917_;
}
else
{
lean_object* v_val_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4998_; 
v_val_4981_ = lean_ctor_get(v_a_4976_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_a_4976_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4983_ = v_a_4976_;
v_isShared_4984_ = v_isSharedCheck_4998_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_val_4981_);
lean_dec(v_a_4976_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4998_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lake_resolveArtifactOutput(v_val_4981_, v_exe_4907_, v___y_4908_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v___x_4979_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v_a_4987_; lean_object* v___x_4989_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
v_a_4987_ = lean_ctor_get(v___x_4985_, 1);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4985_, 2);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 0, v_a_4986_);
v___x_4989_ = v___x_4983_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4986_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
v_r_4918_ = v___x_4989_;
v___y_4919_ = v_a_4987_;
goto v___jp_4917_;
}
}
else
{
lean_object* v_a_4991_; lean_object* v_a_4992_; lean_object* v_log_4993_; uint8_t v_action_4994_; uint8_t v_wantsRebuild_4995_; lean_object* v_trace_4996_; lean_object* v_buildTime_4997_; 
lean_del_object(v___x_4983_);
v_a_4991_ = lean_ctor_get(v___x_4985_, 1);
lean_inc(v_a_4991_);
v_a_4992_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4985_, 2);
v_log_4993_ = lean_ctor_get(v_a_4991_, 0);
lean_inc_ref(v_log_4993_);
v_action_4994_ = lean_ctor_get_uint8(v_a_4991_, sizeof(void*)*3);
v_wantsRebuild_4995_ = lean_ctor_get_uint8(v_a_4991_, sizeof(void*)*3 + 1);
v_trace_4996_ = lean_ctor_get(v_a_4991_, 1);
lean_inc_ref(v_trace_4996_);
v_buildTime_4997_ = lean_ctor_get(v_a_4991_, 2);
lean_inc(v_buildTime_4997_);
lean_dec(v_a_4991_);
v_a_4934_ = v_a_4992_;
v_log_4935_ = v_log_4993_;
v_action_4936_ = v_action_4994_;
v_wantsRebuild_4937_ = v_wantsRebuild_4995_;
v_trace_4938_ = v_trace_4996_;
v_buildTime_4939_ = v_buildTime_4997_;
goto v___jp_4933_;
}
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v_a_5001_; 
lean_del_object(v___x_4971_);
lean_dec_ref(v___y_4908_);
v_a_5000_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_5000_);
v_a_5001_ = lean_ctor_get(v___x_4975_, 1);
lean_inc(v_a_5001_);
lean_dec_ref_known(v___x_4975_, 2);
v_a_4934_ = v_a_5000_;
v_log_4935_ = v_a_5001_;
v_action_4936_ = v_action_4966_;
v_wantsRebuild_4937_ = v_wantsRebuild_4967_;
v_trace_4938_ = v_trace_4968_;
v_buildTime_4939_ = v_buildTime_4969_;
goto v___jp_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_5003_, lean_object* v___y_5004_, lean_object* v_inputHash_5005_, lean_object* v_pkg_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
uint8_t v_exe_boxed_5013_; uint64_t v_inputHash_boxed_5014_; lean_object* v_res_5015_; 
v_exe_boxed_5013_ = lean_unbox(v_exe_5003_);
v_inputHash_boxed_5014_ = lean_unbox_uint64(v_inputHash_5005_);
lean_dec_ref(v_inputHash_5005_);
v_res_5015_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5013_, v___y_5004_, v_inputHash_boxed_5014_, v_pkg_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec(v_a_5007_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5016_, uint64_t v_hash_5017_, lean_object* v_a_5018_, lean_object* v_val_5019_, lean_object* v_file_5020_, lean_object* v___x_5021_, uint8_t v_restore_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
lean_object* v_a_5031_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; uint8_t v___y_5078_; uint8_t v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v_a_5096_; lean_object* v_val_5097_; lean_object* v_a_5098_; lean_object* v_a_5152_; lean_object* v___y_5153_; lean_object* v___x_5155_; lean_object* v_a_5156_; 
lean_inc_ref(v_val_5019_);
lean_inc(v_a_5018_);
lean_inc_ref(v___y_5023_);
v___x_5155_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5016_, v___y_5023_, v_hash_5017_, v_a_5018_, v_val_5019_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
if (lean_obj_tag(v_a_5156_) == 1)
{
lean_object* v_a_5157_; lean_object* v_val_5158_; 
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_val_5019_);
v_a_5157_ = lean_ctor_get(v___x_5155_, 1);
lean_inc(v_a_5157_);
lean_dec_ref(v___x_5155_);
v_val_5158_ = lean_ctor_get(v_a_5156_, 0);
lean_inc(v_val_5158_);
lean_dec_ref_known(v_a_5156_, 1);
v_a_5152_ = v_val_5158_;
v___y_5153_ = v_a_5157_;
goto v___jp_5151_;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5160_; lean_object* v_a_5161_; 
lean_dec(v_a_5156_);
v_a_5159_ = lean_ctor_get(v___x_5155_, 1);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5155_);
v___x_5160_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5016_, v___y_5023_, v_hash_5017_, v_val_5019_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v_a_5159_);
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
lean_inc(v_a_5161_);
if (lean_obj_tag(v_a_5161_) == 1)
{
lean_object* v_a_5162_; lean_object* v_val_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5160_, 1);
lean_inc(v_a_5162_);
lean_dec_ref(v___x_5160_);
v_val_5163_ = lean_ctor_get(v_a_5161_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v_a_5161_, 1);
v_a_5152_ = v_val_5163_;
v___y_5153_ = v_a_5162_;
goto v___jp_5151_;
}
else
{
lean_object* v_a_5164_; 
lean_dec(v_a_5161_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
lean_dec(v_a_5018_);
v_a_5164_ = lean_ctor_get(v___x_5160_, 1);
lean_inc(v_a_5164_);
lean_dec_ref(v___x_5160_);
v_a_5031_ = v_a_5164_;
goto v___jp_5030_;
}
}
v___jp_5030_:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = lean_box(0);
v___x_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5032_);
lean_ctor_set(v___x_5033_, 1, v_a_5031_);
return v___x_5033_;
}
v___jp_5034_:
{
if (v_restore_5022_ == 0)
{
lean_object* v___x_5038_; 
lean_dec_ref(v___y_5035_);
lean_dec_ref(v_file_5020_);
v___x_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___y_5036_);
lean_ctor_set(v___x_5038_, 1, v___y_5037_);
return v___x_5038_;
}
else
{
lean_object* v_log_5039_; uint8_t v_action_5040_; uint8_t v_wantsRebuild_5041_; lean_object* v_trace_5042_; lean_object* v_buildTime_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5073_; 
lean_dec(v___y_5036_);
v_log_5039_ = lean_ctor_get(v___y_5037_, 0);
v_action_5040_ = lean_ctor_get_uint8(v___y_5037_, sizeof(void*)*3);
v_wantsRebuild_5041_ = lean_ctor_get_uint8(v___y_5037_, sizeof(void*)*3 + 1);
v_trace_5042_ = lean_ctor_get(v___y_5037_, 1);
v_buildTime_5043_ = lean_ctor_get(v___y_5037_, 2);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___y_5037_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5045_ = v___y_5037_;
v_isShared_5046_ = v_isSharedCheck_5073_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_buildTime_5043_);
lean_inc(v_trace_5042_);
lean_inc(v_log_5039_);
lean_dec(v___y_5037_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5073_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lake_restoreArtifact(v_file_5020_, v___y_5035_, v_exe_5016_, v_log_5039_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5060_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
v_a_5049_ = lean_ctor_get(v___x_5047_, 1);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5051_ = v___x_5047_;
v_isShared_5052_ = v_isSharedCheck_5060_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_inc(v_a_5048_);
lean_dec(v___x_5047_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5060_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v_a_5049_);
v___x_5054_ = v___x_5045_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5049_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_trace_5042_);
lean_ctor_set(v_reuseFailAlloc_5059_, 2, v_buildTime_5043_);
lean_ctor_set_uint8(v_reuseFailAlloc_5059_, sizeof(void*)*3, v_action_5040_);
lean_ctor_set_uint8(v_reuseFailAlloc_5059_, sizeof(void*)*3 + 1, v_wantsRebuild_5041_);
v___x_5054_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
lean_object* v___x_5055_; lean_object* v___x_5057_; 
v___x_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5055_, 0, v_a_5048_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 1, v___x_5054_);
lean_ctor_set(v___x_5051_, 0, v___x_5055_);
v___x_5057_ = v___x_5051_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v___x_5054_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5072_; 
v_a_5061_ = lean_ctor_get(v___x_5047_, 0);
v_a_5062_ = lean_ctor_get(v___x_5047_, 1);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5064_ = v___x_5047_;
v_isShared_5065_ = v_isSharedCheck_5072_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_inc(v_a_5061_);
lean_dec(v___x_5047_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5072_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v_a_5062_);
v___x_5067_ = v___x_5045_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5062_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_trace_5042_);
lean_ctor_set(v_reuseFailAlloc_5071_, 2, v_buildTime_5043_);
lean_ctor_set_uint8(v_reuseFailAlloc_5071_, sizeof(void*)*3, v_action_5040_);
lean_ctor_set_uint8(v_reuseFailAlloc_5071_, sizeof(void*)*3 + 1, v_wantsRebuild_5041_);
v___x_5067_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
lean_object* v___x_5069_; 
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 1, v___x_5067_);
v___x_5069_ = v___x_5064_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5061_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
}
}
}
v___jp_5074_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5083_, 0, v___y_5082_);
v___x_5084_ = l_Lake_BuildMetadata_ofFetch(v_hash_5017_, v___x_5083_);
v___x_5085_ = l_Lake_BuildMetadata_writeFile(v___x_5021_, v___x_5084_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v___x_5086_; 
lean_dec_ref_known(v___x_5085_, 1);
v___x_5086_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5086_, 0, v___y_5075_);
lean_ctor_set(v___x_5086_, 1, v___y_5077_);
lean_ctor_set(v___x_5086_, 2, v___y_5076_);
lean_ctor_set_uint8(v___x_5086_, sizeof(void*)*3, v___y_5079_);
lean_ctor_set_uint8(v___x_5086_, sizeof(void*)*3 + 1, v___y_5078_);
v___y_5035_ = v___y_5080_;
v___y_5036_ = v___y_5081_;
v___y_5037_ = v___x_5086_;
goto v___jp_5034_;
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
lean_dec_ref(v_file_5020_);
v_a_5087_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5085_, 1);
v___x_5088_ = lean_io_error_to_string(v_a_5087_);
v___x_5089_ = 3;
v___x_5090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5090_, 0, v___x_5088_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*1, v___x_5089_);
v___x_5091_ = lean_array_get_size(v___y_5075_);
v___x_5092_ = lean_array_push(v___y_5075_, v___x_5090_);
v___x_5093_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
lean_ctor_set(v___x_5093_, 1, v___y_5077_);
lean_ctor_set(v___x_5093_, 2, v___y_5076_);
lean_ctor_set_uint8(v___x_5093_, sizeof(void*)*3, v___y_5079_);
lean_ctor_set_uint8(v___x_5093_, sizeof(void*)*3 + 1, v___y_5078_);
v___x_5094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5091_);
lean_ctor_set(v___x_5094_, 1, v___x_5093_);
return v___x_5094_;
}
}
v___jp_5095_:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5017_, v_a_5018_, v_a_5098_);
lean_dec(v_a_5018_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; uint8_t v___x_5101_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5100_);
v___x_5101_ = lean_unbox(v_a_5100_);
lean_dec(v_a_5100_);
if (v___x_5101_ == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5139_; 
v_a_5102_ = lean_ctor_get(v___x_5099_, 1);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5139_ == 0)
{
lean_object* v_unused_5140_; 
v_unused_5140_ = lean_ctor_get(v___x_5099_, 0);
lean_dec(v_unused_5140_);
v___x_5104_ = v___x_5099_;
v_isShared_5105_ = v_isSharedCheck_5139_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5099_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5139_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v_log_5106_; uint8_t v_action_5107_; uint8_t v_wantsRebuild_5108_; lean_object* v_trace_5109_; lean_object* v_buildTime_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5138_; 
v_log_5106_ = lean_ctor_get(v_a_5102_, 0);
v_action_5107_ = lean_ctor_get_uint8(v_a_5102_, sizeof(void*)*3);
v_wantsRebuild_5108_ = lean_ctor_get_uint8(v_a_5102_, sizeof(void*)*3 + 1);
v_trace_5109_ = lean_ctor_get(v_a_5102_, 1);
v_buildTime_5110_ = lean_ctor_get(v_a_5102_, 2);
v_isSharedCheck_5138_ = !lean_is_exclusive(v_a_5102_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5112_ = v_a_5102_;
v_isShared_5113_ = v_isSharedCheck_5138_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_buildTime_5110_);
lean_inc(v_trace_5109_);
lean_inc(v_log_5106_);
lean_dec(v_a_5102_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5138_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lake_removeFileIfExists(v_file_5020_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_descr_5115_; uint64_t v_hash_5116_; lean_object* v_ext_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; 
lean_dec_ref_known(v___x_5114_, 1);
lean_del_object(v___x_5112_);
lean_del_object(v___x_5104_);
v_descr_5115_ = lean_ctor_get(v_val_5097_, 0);
v_hash_5116_ = lean_ctor_get_uint64(v_descr_5115_, sizeof(void*)*1);
v_ext_5117_ = lean_ctor_get(v_descr_5115_, 0);
v___x_5118_ = lean_string_utf8_byte_size(v_ext_5117_);
v___x_5119_ = lean_unsigned_to_nat(0u);
v___x_5120_ = lean_nat_dec_eq(v___x_5118_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5121_ = l_Lake_lowerHexUInt64(v_hash_5116_);
v___x_5122_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5123_ = lean_string_append(v___x_5121_, v___x_5122_);
v___x_5124_ = lean_string_append(v___x_5123_, v_ext_5117_);
v___y_5075_ = v_log_5106_;
v___y_5076_ = v_buildTime_5110_;
v___y_5077_ = v_trace_5109_;
v___y_5078_ = v_wantsRebuild_5108_;
v___y_5079_ = v_action_5107_;
v___y_5080_ = v_val_5097_;
v___y_5081_ = v_a_5096_;
v___y_5082_ = v___x_5124_;
goto v___jp_5074_;
}
else
{
lean_object* v___x_5125_; 
v___x_5125_ = l_Lake_lowerHexUInt64(v_hash_5116_);
v___y_5075_ = v_log_5106_;
v___y_5076_ = v_buildTime_5110_;
v___y_5077_ = v_trace_5109_;
v___y_5078_ = v_wantsRebuild_5108_;
v___y_5079_ = v_action_5107_;
v___y_5080_ = v_val_5097_;
v___y_5081_ = v_a_5096_;
v___y_5082_ = v___x_5125_;
goto v___jp_5074_;
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5127_; uint8_t v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; 
lean_dec_ref(v_val_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5126_ = lean_ctor_get(v___x_5114_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5114_, 1);
v___x_5127_ = lean_io_error_to_string(v_a_5126_);
v___x_5128_ = 3;
v___x_5129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5129_, 0, v___x_5127_);
lean_ctor_set_uint8(v___x_5129_, sizeof(void*)*1, v___x_5128_);
v___x_5130_ = lean_array_get_size(v_log_5106_);
v___x_5131_ = lean_array_push(v_log_5106_, v___x_5129_);
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 0, v___x_5131_);
v___x_5133_ = v___x_5112_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_trace_5109_);
lean_ctor_set(v_reuseFailAlloc_5137_, 2, v_buildTime_5110_);
lean_ctor_set_uint8(v_reuseFailAlloc_5137_, sizeof(void*)*3, v_action_5107_);
lean_ctor_set_uint8(v_reuseFailAlloc_5137_, sizeof(void*)*3 + 1, v_wantsRebuild_5108_);
v___x_5133_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
lean_object* v___x_5135_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set_tag(v___x_5104_, 1);
lean_ctor_set(v___x_5104_, 1, v___x_5133_);
lean_ctor_set(v___x_5104_, 0, v___x_5130_);
v___x_5135_ = v___x_5104_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
}
}
else
{
lean_object* v_a_5141_; 
lean_dec_ref(v___x_5021_);
v_a_5141_ = lean_ctor_get(v___x_5099_, 1);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5099_, 2);
v___y_5035_ = v_val_5097_;
v___y_5036_ = v_a_5096_;
v___y_5037_ = v_a_5141_;
goto v___jp_5034_;
}
}
else
{
lean_object* v_a_5142_; lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec_ref(v_val_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5142_ = lean_ctor_get(v___x_5099_, 0);
v_a_5143_ = lean_ctor_get(v___x_5099_, 1);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5099_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_inc(v_a_5142_);
lean_dec(v___x_5099_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5142_);
lean_ctor_set(v_reuseFailAlloc_5149_, 1, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
v___jp_5151_:
{
lean_object* v___x_5154_; 
lean_inc_ref(v_a_5152_);
v___x_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5154_, 0, v_a_5152_);
v_a_5096_ = v___x_5154_;
v_val_5097_ = v_a_5152_;
v_a_5098_ = v___y_5153_;
goto v___jp_5095_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5165_, lean_object* v_hash_5166_, lean_object* v_a_5167_, lean_object* v_val_5168_, lean_object* v_file_5169_, lean_object* v___x_5170_, lean_object* v_restore_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
uint8_t v_exe_boxed_5179_; uint64_t v_hash_boxed_5180_; uint8_t v_restore_boxed_5181_; lean_object* v_res_5182_; 
v_exe_boxed_5179_ = lean_unbox(v_exe_5165_);
v_hash_boxed_5180_ = lean_unbox_uint64(v_hash_5166_);
lean_dec_ref(v_hash_5166_);
v_restore_boxed_5181_ = lean_unbox(v_restore_5171_);
v_res_5182_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5179_, v_hash_boxed_5180_, v_a_5167_, v_val_5168_, v_file_5169_, v___x_5170_, v_restore_boxed_5181_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec(v___y_5173_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5183_, lean_object* v_file_5184_, lean_object* v_ext_5185_, uint8_t v_text_5186_, uint8_t v_exe_5187_, uint8_t v___y_5188_, lean_object* v_val_5189_, uint64_t v_hash_5190_, uint8_t v_a_5191_, lean_object* v_____r_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
uint8_t v___x_5200_; uint8_t v___x_5201_; 
v___x_5200_ = 1;
v___x_5201_ = l_Lake_instDecidableEqOutputStatus(v_a_5183_, v___x_5200_);
if (v___x_5201_ == 0)
{
lean_object* v_toContext_5202_; lean_object* v_log_5203_; uint8_t v_action_5204_; uint8_t v_wantsRebuild_5205_; lean_object* v_trace_5206_; lean_object* v_buildTime_5207_; lean_object* v_lakeCache_5208_; lean_object* v___x_5209_; 
v_toContext_5202_ = lean_ctor_get(v___y_5197_, 1);
v_log_5203_ = lean_ctor_get(v___y_5198_, 0);
v_action_5204_ = lean_ctor_get_uint8(v___y_5198_, sizeof(void*)*3);
v_wantsRebuild_5205_ = lean_ctor_get_uint8(v___y_5198_, sizeof(void*)*3 + 1);
v_trace_5206_ = lean_ctor_get(v___y_5198_, 1);
v_buildTime_5207_ = lean_ctor_get(v___y_5198_, 2);
v_lakeCache_5208_ = lean_ctor_get(v_toContext_5202_, 2);
lean_inc_ref(v_lakeCache_5208_);
v___x_5209_ = l_Lake_Cache_saveArtifact(v_lakeCache_5208_, v_file_5184_, v_ext_5185_, v_text_5186_, v_exe_5187_, v___y_5188_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5251_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5251_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5251_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_descr_5214_; uint64_t v_hash_5215_; lean_object* v_ext_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___y_5220_; lean_object* v___x_5243_; lean_object* v___x_5244_; uint8_t v___x_5245_; 
v_descr_5214_ = lean_ctor_get(v_a_5210_, 0);
v_hash_5215_ = lean_ctor_get_uint64(v_descr_5214_, sizeof(void*)*1);
v_ext_5216_ = lean_ctor_get(v_descr_5214_, 0);
v___x_5217_ = l_Lake_Package_cacheScope(v_val_5189_);
v___x_5218_ = lean_box(0);
v___x_5243_ = lean_string_utf8_byte_size(v_ext_5216_);
v___x_5244_ = lean_unsigned_to_nat(0u);
v___x_5245_ = lean_nat_dec_eq(v___x_5243_, v___x_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5246_ = l_Lake_lowerHexUInt64(v_hash_5215_);
v___x_5247_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5248_ = lean_string_append(v___x_5246_, v___x_5247_);
v___x_5249_ = lean_string_append(v___x_5248_, v_ext_5216_);
v___y_5220_ = v___x_5249_;
goto v___jp_5219_;
}
else
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Lake_lowerHexUInt64(v_hash_5215_);
v___y_5220_ = v___x_5250_;
goto v___jp_5219_;
}
v___jp_5219_:
{
lean_object* v___x_5222_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set_tag(v___x_5212_, 3);
lean_ctor_set(v___x_5212_, 0, v___y_5220_);
v___x_5222_ = v___x_5212_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___y_5220_);
v___x_5222_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5223_; 
lean_inc_ref(v_lakeCache_5208_);
v___x_5223_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5208_, v___x_5217_, v_hash_5190_, v___x_5222_, v___x_5218_, v___x_5218_, v_a_5191_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v___x_5224_; 
lean_dec_ref_known(v___x_5223_, 1);
v___x_5224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5224_, 0, v_a_5210_);
lean_ctor_set(v___x_5224_, 1, v___y_5198_);
return v___x_5224_;
}
else
{
lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5238_; 
lean_inc(v_buildTime_5207_);
lean_inc_ref(v_trace_5206_);
lean_inc_ref(v_log_5203_);
lean_dec(v_a_5210_);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___y_5198_);
if (v_isSharedCheck_5238_ == 0)
{
lean_object* v_unused_5239_; lean_object* v_unused_5240_; lean_object* v_unused_5241_; 
v_unused_5239_ = lean_ctor_get(v___y_5198_, 2);
lean_dec(v_unused_5239_);
v_unused_5240_ = lean_ctor_get(v___y_5198_, 1);
lean_dec(v_unused_5240_);
v_unused_5241_ = lean_ctor_get(v___y_5198_, 0);
lean_dec(v_unused_5241_);
v___x_5226_ = v___y_5198_;
v_isShared_5227_ = v_isSharedCheck_5238_;
goto v_resetjp_5225_;
}
else
{
lean_dec(v___y_5198_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5238_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v_a_5228_; lean_object* v___x_5229_; uint8_t v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5235_; 
v_a_5228_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5223_, 1);
v___x_5229_ = lean_io_error_to_string(v_a_5228_);
v___x_5230_ = 3;
v___x_5231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5231_, 0, v___x_5229_);
lean_ctor_set_uint8(v___x_5231_, sizeof(void*)*1, v___x_5230_);
v___x_5232_ = lean_array_get_size(v_log_5203_);
v___x_5233_ = lean_array_push(v_log_5203_, v___x_5231_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 0, v___x_5233_);
v___x_5235_ = v___x_5226_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5233_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v_trace_5206_);
lean_ctor_set(v_reuseFailAlloc_5237_, 2, v_buildTime_5207_);
lean_ctor_set_uint8(v_reuseFailAlloc_5237_, sizeof(void*)*3, v_action_5204_);
lean_ctor_set_uint8(v_reuseFailAlloc_5237_, sizeof(void*)*3 + 1, v_wantsRebuild_5205_);
v___x_5235_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
lean_object* v___x_5236_; 
v___x_5236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5232_);
lean_ctor_set(v___x_5236_, 1, v___x_5235_);
return v___x_5236_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5265_; 
lean_inc(v_buildTime_5207_);
lean_inc_ref(v_trace_5206_);
lean_inc_ref(v_log_5203_);
lean_dec_ref(v_val_5189_);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___y_5198_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; lean_object* v_unused_5267_; lean_object* v_unused_5268_; 
v_unused_5266_ = lean_ctor_get(v___y_5198_, 2);
lean_dec(v_unused_5266_);
v_unused_5267_ = lean_ctor_get(v___y_5198_, 1);
lean_dec(v_unused_5267_);
v_unused_5268_ = lean_ctor_get(v___y_5198_, 0);
lean_dec(v_unused_5268_);
v___x_5253_ = v___y_5198_;
v_isShared_5254_ = v_isSharedCheck_5265_;
goto v_resetjp_5252_;
}
else
{
lean_dec(v___y_5198_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5265_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v_a_5255_; lean_object* v___x_5256_; uint8_t v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5262_; 
v_a_5255_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5255_);
lean_dec_ref_known(v___x_5209_, 1);
v___x_5256_ = lean_io_error_to_string(v_a_5255_);
v___x_5257_ = 3;
v___x_5258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5258_, 0, v___x_5256_);
lean_ctor_set_uint8(v___x_5258_, sizeof(void*)*1, v___x_5257_);
v___x_5259_ = lean_array_get_size(v_log_5203_);
v___x_5260_ = lean_array_push(v_log_5203_, v___x_5258_);
if (v_isShared_5254_ == 0)
{
lean_ctor_set(v___x_5253_, 0, v___x_5260_);
v___x_5262_ = v___x_5253_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5260_);
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v_trace_5206_);
lean_ctor_set(v_reuseFailAlloc_5264_, 2, v_buildTime_5207_);
lean_ctor_set_uint8(v_reuseFailAlloc_5264_, sizeof(void*)*3, v_action_5204_);
lean_ctor_set_uint8(v_reuseFailAlloc_5264_, sizeof(void*)*3 + 1, v_wantsRebuild_5205_);
v___x_5262_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; 
v___x_5263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5259_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
return v___x_5263_;
}
}
}
}
else
{
lean_object* v___x_5269_; 
lean_dec_ref(v_val_5189_);
v___x_5269_ = l_Lake_computeArtifact___redArg(v_file_5184_, v_ext_5185_, v_text_5186_, v___y_5197_, v___y_5198_);
return v___x_5269_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5270_ = _args[0];
lean_object* v_file_5271_ = _args[1];
lean_object* v_ext_5272_ = _args[2];
lean_object* v_text_5273_ = _args[3];
lean_object* v_exe_5274_ = _args[4];
lean_object* v___y_5275_ = _args[5];
lean_object* v_val_5276_ = _args[6];
lean_object* v_hash_5277_ = _args[7];
lean_object* v_a_5278_ = _args[8];
lean_object* v_____r_5279_ = _args[9];
lean_object* v___y_5280_ = _args[10];
lean_object* v___y_5281_ = _args[11];
lean_object* v___y_5282_ = _args[12];
lean_object* v___y_5283_ = _args[13];
lean_object* v___y_5284_ = _args[14];
lean_object* v___y_5285_ = _args[15];
lean_object* v___y_5286_ = _args[16];
_start:
{
uint8_t v_a_299362__boxed_5287_; uint8_t v_text_boxed_5288_; uint8_t v_exe_boxed_5289_; uint8_t v___y_299363__boxed_5290_; uint64_t v_hash_boxed_5291_; uint8_t v_a_299365__boxed_5292_; lean_object* v_res_5293_; 
v_a_299362__boxed_5287_ = lean_unbox(v_a_5270_);
v_text_boxed_5288_ = lean_unbox(v_text_5273_);
v_exe_boxed_5289_ = lean_unbox(v_exe_5274_);
v___y_299363__boxed_5290_ = lean_unbox(v___y_5275_);
v_hash_boxed_5291_ = lean_unbox_uint64(v_hash_5277_);
lean_dec_ref(v_hash_5277_);
v_a_299365__boxed_5292_ = lean_unbox(v_a_5278_);
v_res_5293_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_299362__boxed_5287_, v_file_5271_, v_ext_5272_, v_text_boxed_5288_, v_exe_boxed_5289_, v___y_299363__boxed_5290_, v_val_5276_, v_hash_boxed_5291_, v_a_299365__boxed_5292_, v_____r_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5294_, lean_object* v_build_5295_, uint8_t v_text_5296_, lean_object* v_ext_5297_, uint8_t v_restore_5298_, uint8_t v_exe_5299_, uint8_t v_platformIndependent_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v_log_5308_; uint8_t v_action_5309_; uint8_t v_wantsRebuild_5310_; lean_object* v_trace_5311_; lean_object* v_buildTime_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5573_; 
v_log_5308_ = lean_ctor_get(v_a_5306_, 0);
v_action_5309_ = lean_ctor_get_uint8(v_a_5306_, sizeof(void*)*3);
v_wantsRebuild_5310_ = lean_ctor_get_uint8(v_a_5306_, sizeof(void*)*3 + 1);
v_trace_5311_ = lean_ctor_get(v_a_5306_, 1);
v_buildTime_5312_ = lean_ctor_get(v_a_5306_, 2);
v_isSharedCheck_5573_ = !lean_is_exclusive(v_a_5306_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5314_ = v_a_5306_;
v_isShared_5315_ = v_isSharedCheck_5573_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_buildTime_5312_);
lean_inc(v_trace_5311_);
lean_inc(v_log_5308_);
lean_dec(v_a_5306_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5573_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v_art_5319_; lean_object* v___y_5320_; lean_object* v___y_5336_; lean_object* v_log_5337_; uint8_t v_action_5338_; uint8_t v_wantsRebuild_5339_; lean_object* v_buildTime_5340_; lean_object* v___x_5346_; 
v___x_5316_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5294_);
v___x_5317_ = lean_string_append(v_file_5294_, v___x_5316_);
lean_inc_ref(v___x_5317_);
v___x_5346_ = l_Lake_readTraceFile(v___x_5317_, v_log_5308_);
if (lean_obj_tag(v___x_5346_) == 0)
{
if (lean_obj_tag(v_a_5302_) == 1)
{
lean_object* v_a_5347_; lean_object* v_a_5348_; lean_object* v_val_5349_; uint64_t v_hash_5350_; lean_object* v_mtime_5351_; lean_object* v___y_5353_; lean_object* v___y_5354_; uint8_t v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v___y_5359_; uint8_t v___y_5360_; lean_object* v___y_5361_; lean_object* v_wsIdx_5365_; lean_object* v_config_5366_; lean_object* v_a_5368_; lean_object* v_a_5369_; lean_object* v___y_5399_; lean_object* v_enableArtifactCache_x3f_5402_; lean_object* v_restoreAllArtifacts_x3f_5403_; uint8_t v___y_5405_; lean_object* v___y_5406_; uint8_t v___y_5407_; uint8_t v___y_5446_; uint8_t v___y_5447_; uint8_t v_a_5448_; lean_object* v_a_5449_; uint8_t v___y_5451_; lean_object* v_a_5452_; uint8_t v___y_5469_; uint8_t v_a_5470_; lean_object* v_a_5471_; lean_object* v_a_5474_; uint8_t v_a_5506_; lean_object* v_a_5507_; lean_object* v___x_5523_; 
v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_a_5347_);
v_a_5348_ = lean_ctor_get(v___x_5346_, 1);
lean_inc(v_a_5348_);
lean_dec_ref_known(v___x_5346_, 2);
v_val_5349_ = lean_ctor_get(v_a_5302_, 0);
v_hash_5350_ = lean_ctor_get_uint64(v_trace_5311_, sizeof(void*)*3);
v_mtime_5351_ = lean_ctor_get(v_trace_5311_, 2);
v_wsIdx_5365_ = lean_ctor_get(v_val_5349_, 0);
v_config_5366_ = lean_ctor_get(v_val_5349_, 6);
v_enableArtifactCache_x3f_5402_ = lean_ctor_get(v_config_5366_, 24);
v_restoreAllArtifacts_x3f_5403_ = lean_ctor_get(v_config_5366_, 25);
lean_inc_ref(v_trace_5311_);
v___x_5523_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5523_, 0, v_a_5348_);
lean_ctor_set(v___x_5523_, 1, v_trace_5311_);
lean_ctor_set(v___x_5523_, 2, v_buildTime_5312_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*3, v_action_5309_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*3 + 1, v_wantsRebuild_5310_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5402_) == 0)
{
lean_object* v_toContext_5524_; lean_object* v_lakeEnv_5525_; lean_object* v_enableArtifactCache_x3f_5526_; 
v_toContext_5524_ = lean_ctor_get(v_a_5305_, 1);
v_lakeEnv_5525_ = lean_ctor_get(v_toContext_5524_, 0);
v_enableArtifactCache_x3f_5526_ = lean_ctor_get(v_lakeEnv_5525_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5526_) == 0)
{
lean_object* v_packages_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v_config_5530_; lean_object* v_enableArtifactCache_x3f_5531_; 
v_packages_5527_ = lean_ctor_get(v_toContext_5524_, 4);
v___x_5528_ = lean_unsigned_to_nat(0u);
v___x_5529_ = lean_array_fget_borrowed(v_packages_5527_, v___x_5528_);
v_config_5530_ = lean_ctor_get(v___x_5529_, 6);
v_enableArtifactCache_x3f_5531_ = lean_ctor_get(v_config_5530_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5531_) == 0)
{
v_a_5474_ = v___x_5523_;
goto v___jp_5473_;
}
else
{
lean_object* v_val_5532_; uint8_t v___x_5533_; 
v_val_5532_ = lean_ctor_get(v_enableArtifactCache_x3f_5531_, 0);
v___x_5533_ = lean_unbox(v_val_5532_);
v_a_5506_ = v___x_5533_;
v_a_5507_ = v___x_5523_;
goto v___jp_5505_;
}
}
else
{
lean_object* v_val_5534_; uint8_t v___x_5535_; 
v_val_5534_ = lean_ctor_get(v_enableArtifactCache_x3f_5526_, 0);
v___x_5535_ = lean_unbox(v_val_5534_);
v_a_5506_ = v___x_5535_;
v_a_5507_ = v___x_5523_;
goto v___jp_5505_;
}
}
else
{
lean_object* v_val_5536_; uint8_t v___x_5537_; 
v_val_5536_ = lean_ctor_get(v_enableArtifactCache_x3f_5402_, 0);
v___x_5537_ = lean_unbox(v_val_5536_);
v_a_5506_ = v___x_5537_;
v_a_5507_ = v___x_5523_;
goto v___jp_5505_;
}
v___jp_5352_:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
lean_dec_ref(v___y_5356_);
v___x_5362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5362_, 0, v___y_5361_);
v___x_5363_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5350_, v___x_5362_, v___y_5353_, v_platformIndependent_5300_);
v___x_5364_ = lean_st_ref_set(v___y_5357_, v___x_5363_);
v___y_5336_ = v___y_5358_;
v_log_5337_ = v___y_5354_;
v_action_5338_ = v___y_5355_;
v_wantsRebuild_5339_ = v___y_5360_;
v_buildTime_5340_ = v___y_5359_;
goto v___jp_5335_;
}
v___jp_5367_:
{
lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5370_ = lean_unsigned_to_nat(0u);
v___x_5371_ = lean_nat_dec_eq(v_wsIdx_5365_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_object* v_log_5372_; uint8_t v_action_5373_; uint8_t v_wantsRebuild_5374_; lean_object* v_buildTime_5375_; 
v_log_5372_ = lean_ctor_get(v_a_5369_, 0);
lean_inc_ref(v_log_5372_);
v_action_5373_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3);
v_wantsRebuild_5374_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3 + 1);
v_buildTime_5375_ = lean_ctor_get(v_a_5369_, 2);
lean_inc(v_buildTime_5375_);
lean_dec_ref(v_a_5369_);
v___y_5336_ = v_a_5368_;
v_log_5337_ = v_log_5372_;
v_action_5338_ = v_action_5373_;
v_wantsRebuild_5339_ = v_wantsRebuild_5374_;
v_buildTime_5340_ = v_buildTime_5375_;
goto v___jp_5335_;
}
else
{
lean_object* v_outputsRef_x3f_5376_; 
v_outputsRef_x3f_5376_ = lean_ctor_get(v_a_5305_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5376_) == 1)
{
lean_object* v_log_5377_; uint8_t v_action_5378_; uint8_t v_wantsRebuild_5379_; lean_object* v_trace_5380_; lean_object* v_buildTime_5381_; lean_object* v_val_5382_; lean_object* v___x_5383_; lean_object* v_descr_5384_; uint64_t v_hash_5385_; lean_object* v_ext_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; 
v_log_5377_ = lean_ctor_get(v_a_5369_, 0);
lean_inc_ref(v_log_5377_);
v_action_5378_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3);
v_wantsRebuild_5379_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3 + 1);
v_trace_5380_ = lean_ctor_get(v_a_5369_, 1);
lean_inc_ref(v_trace_5380_);
v_buildTime_5381_ = lean_ctor_get(v_a_5369_, 2);
lean_inc(v_buildTime_5381_);
lean_dec_ref(v_a_5369_);
v_val_5382_ = lean_ctor_get(v_outputsRef_x3f_5376_, 0);
v___x_5383_ = lean_st_ref_take(v_val_5382_);
v_descr_5384_ = lean_ctor_get(v_a_5368_, 0);
v_hash_5385_ = lean_ctor_get_uint64(v_descr_5384_, sizeof(void*)*1);
v_ext_5386_ = lean_ctor_get(v_descr_5384_, 0);
v___x_5387_ = lean_string_utf8_byte_size(v_ext_5386_);
v___x_5388_ = lean_nat_dec_eq(v___x_5387_, v___x_5370_);
if (v___x_5388_ == 0)
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5389_ = l_Lake_lowerHexUInt64(v_hash_5385_);
v___x_5390_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5391_ = lean_string_append(v___x_5389_, v___x_5390_);
v___x_5392_ = lean_string_append(v___x_5391_, v_ext_5386_);
v___y_5353_ = v___x_5383_;
v___y_5354_ = v_log_5377_;
v___y_5355_ = v_action_5378_;
v___y_5356_ = v_trace_5380_;
v___y_5357_ = v_val_5382_;
v___y_5358_ = v_a_5368_;
v___y_5359_ = v_buildTime_5381_;
v___y_5360_ = v_wantsRebuild_5379_;
v___y_5361_ = v___x_5392_;
goto v___jp_5352_;
}
else
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Lake_lowerHexUInt64(v_hash_5385_);
v___y_5353_ = v___x_5383_;
v___y_5354_ = v_log_5377_;
v___y_5355_ = v_action_5378_;
v___y_5356_ = v_trace_5380_;
v___y_5357_ = v_val_5382_;
v___y_5358_ = v_a_5368_;
v___y_5359_ = v_buildTime_5381_;
v___y_5360_ = v_wantsRebuild_5379_;
v___y_5361_ = v___x_5393_;
goto v___jp_5352_;
}
}
else
{
lean_object* v_log_5394_; uint8_t v_action_5395_; uint8_t v_wantsRebuild_5396_; lean_object* v_buildTime_5397_; 
v_log_5394_ = lean_ctor_get(v_a_5369_, 0);
lean_inc_ref(v_log_5394_);
v_action_5395_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3);
v_wantsRebuild_5396_ = lean_ctor_get_uint8(v_a_5369_, sizeof(void*)*3 + 1);
v_buildTime_5397_ = lean_ctor_get(v_a_5369_, 2);
lean_inc(v_buildTime_5397_);
lean_dec_ref(v_a_5369_);
v___y_5336_ = v_a_5368_;
v_log_5337_ = v_log_5394_;
v_action_5338_ = v_action_5395_;
v_wantsRebuild_5339_ = v_wantsRebuild_5396_;
v_buildTime_5340_ = v_buildTime_5397_;
goto v___jp_5335_;
}
}
}
v___jp_5398_:
{
if (lean_obj_tag(v___y_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v_a_5401_; 
v_a_5400_ = lean_ctor_get(v___y_5399_, 0);
lean_inc(v_a_5400_);
v_a_5401_ = lean_ctor_get(v___y_5399_, 1);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___y_5399_, 2);
v_a_5368_ = v_a_5400_;
v_a_5369_ = v_a_5401_;
goto v___jp_5367_;
}
else
{
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
return v___y_5399_;
}
}
v___jp_5404_:
{
lean_object* v___x_5408_; 
lean_inc_ref(v_a_5301_);
lean_inc_ref(v___x_5317_);
lean_inc_ref(v_file_5294_);
lean_inc(v_val_5349_);
lean_inc(v_a_5347_);
v___x_5408_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5299_, v_hash_5350_, v_a_5347_, v_val_5349_, v_file_5294_, v___x_5317_, v___y_5407_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v___y_5406_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
lean_inc(v_a_5409_);
if (lean_obj_tag(v_a_5409_) == 1)
{
lean_object* v_a_5410_; lean_object* v_val_5411_; 
lean_dec(v_a_5347_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5410_ = lean_ctor_get(v___x_5408_, 1);
lean_inc(v_a_5410_);
lean_dec_ref_known(v___x_5408_, 2);
v_val_5411_ = lean_ctor_get(v_a_5409_, 0);
lean_inc(v_val_5411_);
lean_dec_ref_known(v_a_5409_, 1);
v_a_5368_ = v_val_5411_;
v_a_5369_ = v_a_5410_;
goto v___jp_5367_;
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5413_; 
lean_dec(v_a_5409_);
v_a_5412_ = lean_ctor_get(v___x_5408_, 1);
lean_inc(v_a_5412_);
lean_dec_ref_known(v___x_5408_, 2);
v___x_5413_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5301_, v_file_5294_, v_trace_5311_, v_a_5347_, v_mtime_5351_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5412_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v_a_5415_; uint8_t v___x_5416_; uint8_t v___x_5417_; uint8_t v___x_5418_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc(v_a_5414_);
v_a_5415_ = lean_ctor_get(v___x_5413_, 1);
lean_inc(v_a_5415_);
lean_dec_ref_known(v___x_5413_, 2);
v___x_5416_ = 0;
v___x_5417_ = lean_unbox(v_a_5414_);
v___x_5418_ = l_Lake_instDecidableEqOutputStatus(v___x_5417_, v___x_5416_);
if (v___x_5418_ == 0)
{
lean_object* v___x_5419_; uint8_t v___x_5420_; lean_object* v___x_5421_; 
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_build_5295_);
v___x_5419_ = lean_box(0);
v___x_5420_ = lean_unbox(v_a_5414_);
lean_dec(v_a_5414_);
lean_inc(v_val_5349_);
v___x_5421_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5420_, v_file_5294_, v_ext_5297_, v_text_5296_, v_exe_5299_, v___y_5407_, v_val_5349_, v_hash_5350_, v___y_5405_, v___x_5419_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5415_);
lean_dec_ref(v_a_5301_);
v___y_5399_ = v___x_5421_;
goto v___jp_5398_;
}
else
{
lean_object* v___x_5422_; 
lean_inc_ref(v_a_5301_);
lean_inc_ref(v___x_5317_);
lean_inc_ref(v_ext_5297_);
lean_inc_ref(v_file_5294_);
v___x_5422_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5294_, v_build_5295_, v_text_5296_, v_ext_5297_, v_trace_5311_, v___x_5317_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5415_);
lean_dec_ref(v_trace_5311_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; lean_object* v___x_5426_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 1);
lean_inc(v_a_5423_);
lean_dec_ref_known(v___x_5422_, 2);
v___x_5424_ = lean_box(0);
v___x_5425_ = lean_unbox(v_a_5414_);
lean_dec(v_a_5414_);
lean_inc(v_val_5349_);
v___x_5426_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5425_, v_file_5294_, v_ext_5297_, v_text_5296_, v_exe_5299_, v___y_5407_, v_val_5349_, v_hash_5350_, v___y_5405_, v___x_5424_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5423_);
lean_dec_ref(v_a_5301_);
v___y_5399_ = v___x_5426_;
goto v___jp_5398_;
}
else
{
lean_dec(v_a_5414_);
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_file_5294_);
return v___x_5422_;
}
}
}
else
{
lean_object* v_a_5427_; lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5427_ = lean_ctor_get(v___x_5413_, 0);
v_a_5428_ = lean_ctor_get(v___x_5413_, 1);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5413_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_inc(v_a_5427_);
lean_dec(v___x_5413_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5427_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
}
else
{
lean_object* v_a_5436_; lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_dec(v_a_5347_);
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5436_ = lean_ctor_get(v___x_5408_, 0);
v_a_5437_ = lean_ctor_get(v___x_5408_, 1);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5408_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_inc(v_a_5436_);
lean_dec(v___x_5408_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5436_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
v___jp_5445_:
{
if (v_restore_5298_ == 0)
{
v___y_5405_ = v___y_5446_;
v___y_5406_ = v_a_5449_;
v___y_5407_ = v_a_5448_;
goto v___jp_5404_;
}
else
{
v___y_5405_ = v___y_5446_;
v___y_5406_ = v_a_5449_;
v___y_5407_ = v___y_5447_;
goto v___jp_5404_;
}
}
v___jp_5450_:
{
lean_object* v___x_5453_; 
lean_inc_ref(v_a_5301_);
lean_inc_ref(v___x_5317_);
lean_inc_ref(v_file_5294_);
lean_inc(v_val_5349_);
v___x_5453_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5299_, v_hash_5350_, v_a_5347_, v_val_5349_, v_file_5294_, v___x_5317_, v___y_5451_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5452_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v_a_5454_);
if (lean_obj_tag(v_a_5454_) == 1)
{
lean_object* v_a_5455_; lean_object* v_val_5456_; 
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5455_ = lean_ctor_get(v___x_5453_, 1);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5453_, 2);
v_val_5456_ = lean_ctor_get(v_a_5454_, 0);
lean_inc(v_val_5456_);
lean_dec_ref_known(v_a_5454_, 1);
v_a_5368_ = v_val_5456_;
v_a_5369_ = v_a_5455_;
goto v___jp_5367_;
}
else
{
lean_object* v_a_5457_; lean_object* v___x_5458_; 
lean_dec(v_a_5454_);
v_a_5457_ = lean_ctor_get(v___x_5453_, 1);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5453_, 2);
lean_inc_ref(v___x_5317_);
v___x_5458_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5294_, v_build_5295_, v_text_5296_, v_ext_5297_, v_trace_5311_, v___x_5317_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5457_);
lean_dec_ref(v_trace_5311_);
v___y_5399_ = v___x_5458_;
goto v___jp_5398_;
}
}
else
{
lean_object* v_a_5459_; lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5459_ = lean_ctor_get(v___x_5453_, 0);
v_a_5460_ = lean_ctor_get(v___x_5453_, 1);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5453_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_inc(v_a_5459_);
lean_dec(v___x_5453_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5465_; 
if (v_isShared_5463_ == 0)
{
v___x_5465_ = v___x_5462_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5459_);
lean_ctor_set(v_reuseFailAlloc_5466_, 1, v_a_5460_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
v___jp_5468_:
{
if (v_a_5470_ == 0)
{
lean_object* v___x_5472_; 
lean_dec(v_a_5347_);
lean_inc_ref(v___x_5317_);
v___x_5472_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5294_, v_build_5295_, v_text_5296_, v_ext_5297_, v_trace_5311_, v___x_5317_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5471_);
lean_dec_ref(v_trace_5311_);
v___y_5399_ = v___x_5472_;
goto v___jp_5398_;
}
else
{
v___y_5451_ = v___y_5469_;
v_a_5452_ = v_a_5471_;
goto v___jp_5450_;
}
}
v___jp_5473_:
{
lean_object* v___x_5475_; 
lean_inc(v_a_5347_);
v___x_5475_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5301_, v_file_5294_, v_trace_5311_, v_a_5347_, v_mtime_5351_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5474_);
if (lean_obj_tag(v___x_5475_) == 0)
{
lean_object* v_a_5476_; lean_object* v_a_5477_; uint8_t v___x_5478_; uint8_t v___x_5479_; uint8_t v___x_5480_; 
v_a_5476_ = lean_ctor_get(v___x_5475_, 0);
lean_inc(v_a_5476_);
v_a_5477_ = lean_ctor_get(v___x_5475_, 1);
lean_inc(v_a_5477_);
lean_dec_ref_known(v___x_5475_, 2);
v___x_5478_ = 0;
v___x_5479_ = lean_unbox(v_a_5476_);
lean_dec(v_a_5476_);
v___x_5480_ = l_Lake_instDecidableEqOutputStatus(v___x_5479_, v___x_5478_);
if (v___x_5480_ == 0)
{
lean_object* v___x_5481_; 
lean_dec(v_a_5347_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_build_5295_);
v___x_5481_ = l_Lake_computeArtifact___redArg(v_file_5294_, v_ext_5297_, v_text_5296_, v_a_5305_, v_a_5477_);
v___y_5399_ = v___x_5481_;
goto v___jp_5398_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5402_) == 0)
{
lean_object* v_toContext_5482_; lean_object* v_lakeEnv_5483_; lean_object* v_enableArtifactCache_x3f_5484_; 
v_toContext_5482_ = lean_ctor_get(v_a_5305_, 1);
v_lakeEnv_5483_ = lean_ctor_get(v_toContext_5482_, 0);
v_enableArtifactCache_x3f_5484_ = lean_ctor_get(v_lakeEnv_5483_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5484_) == 0)
{
lean_object* v_packages_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v_config_5488_; lean_object* v_enableArtifactCache_x3f_5489_; 
v_packages_5485_ = lean_ctor_get(v_toContext_5482_, 4);
v___x_5486_ = lean_unsigned_to_nat(0u);
v___x_5487_ = lean_array_fget_borrowed(v_packages_5485_, v___x_5486_);
v_config_5488_ = lean_ctor_get(v___x_5487_, 6);
v_enableArtifactCache_x3f_5489_ = lean_ctor_get(v_config_5488_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5489_) == 0)
{
v___y_5451_ = v___x_5480_;
v_a_5452_ = v_a_5477_;
goto v___jp_5450_;
}
else
{
lean_object* v_val_5490_; uint8_t v___x_5491_; 
v_val_5490_ = lean_ctor_get(v_enableArtifactCache_x3f_5489_, 0);
v___x_5491_ = lean_unbox(v_val_5490_);
v___y_5469_ = v___x_5480_;
v_a_5470_ = v___x_5491_;
v_a_5471_ = v_a_5477_;
goto v___jp_5468_;
}
}
else
{
lean_object* v_val_5492_; uint8_t v___x_5493_; 
v_val_5492_ = lean_ctor_get(v_enableArtifactCache_x3f_5484_, 0);
v___x_5493_ = lean_unbox(v_val_5492_);
v___y_5469_ = v___x_5480_;
v_a_5470_ = v___x_5493_;
v_a_5471_ = v_a_5477_;
goto v___jp_5468_;
}
}
else
{
lean_object* v_val_5494_; uint8_t v___x_5495_; 
v_val_5494_ = lean_ctor_get(v_enableArtifactCache_x3f_5402_, 0);
v___x_5495_ = lean_unbox(v_val_5494_);
v___y_5469_ = v___x_5480_;
v_a_5470_ = v___x_5495_;
v_a_5471_ = v_a_5477_;
goto v___jp_5468_;
}
}
}
else
{
lean_object* v_a_5496_; lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5504_; 
lean_dec(v_a_5347_);
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5496_ = lean_ctor_get(v___x_5475_, 0);
v_a_5497_ = lean_ctor_get(v___x_5475_, 1);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5475_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5499_ = v___x_5475_;
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_inc(v_a_5496_);
lean_dec(v___x_5475_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_a_5496_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_a_5497_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
v___jp_5505_:
{
if (v_a_5506_ == 0)
{
v_a_5474_ = v_a_5507_;
goto v___jp_5473_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5403_) == 0)
{
lean_object* v_toContext_5508_; lean_object* v_lakeEnv_5509_; lean_object* v_restoreAllArtifacts_x3f_5510_; 
v_toContext_5508_ = lean_ctor_get(v_a_5305_, 1);
v_lakeEnv_5509_ = lean_ctor_get(v_toContext_5508_, 0);
v_restoreAllArtifacts_x3f_5510_ = lean_ctor_get(v_lakeEnv_5509_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5510_) == 0)
{
lean_object* v_packages_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v_config_5514_; lean_object* v_restoreAllArtifacts_x3f_5515_; 
v_packages_5511_ = lean_ctor_get(v_toContext_5508_, 4);
v___x_5512_ = lean_unsigned_to_nat(0u);
v___x_5513_ = lean_array_fget_borrowed(v_packages_5511_, v___x_5512_);
v_config_5514_ = lean_ctor_get(v___x_5513_, 6);
v_restoreAllArtifacts_x3f_5515_ = lean_ctor_get(v_config_5514_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5515_) == 0)
{
uint8_t v___x_5516_; 
v___x_5516_ = 0;
v___y_5446_ = v_a_5506_;
v___y_5447_ = v_a_5506_;
v_a_5448_ = v___x_5516_;
v_a_5449_ = v_a_5507_;
goto v___jp_5445_;
}
else
{
lean_object* v_val_5517_; uint8_t v___x_5518_; 
v_val_5517_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5515_, 0);
v___x_5518_ = lean_unbox(v_val_5517_);
v___y_5446_ = v_a_5506_;
v___y_5447_ = v_a_5506_;
v_a_5448_ = v___x_5518_;
v_a_5449_ = v_a_5507_;
goto v___jp_5445_;
}
}
else
{
lean_object* v_val_5519_; uint8_t v___x_5520_; 
v_val_5519_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5510_, 0);
v___x_5520_ = lean_unbox(v_val_5519_);
v___y_5446_ = v_a_5506_;
v___y_5447_ = v_a_5506_;
v_a_5448_ = v___x_5520_;
v_a_5449_ = v_a_5507_;
goto v___jp_5445_;
}
}
else
{
lean_object* v_val_5521_; uint8_t v___x_5522_; 
v_val_5521_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5403_, 0);
v___x_5522_ = lean_unbox(v_val_5521_);
v___y_5446_ = v_a_5506_;
v___y_5447_ = v_a_5506_;
v_a_5448_ = v___x_5522_;
v_a_5449_ = v_a_5507_;
goto v___jp_5445_;
}
}
}
}
else
{
lean_object* v_a_5538_; lean_object* v_a_5539_; lean_object* v_mtime_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; 
lean_del_object(v___x_5314_);
v_a_5538_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_a_5538_);
v_a_5539_ = lean_ctor_get(v___x_5346_, 1);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5346_, 2);
v_mtime_5540_ = lean_ctor_get(v_trace_5311_, 2);
lean_inc_ref(v_trace_5311_);
v___x_5541_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5541_, 0, v_a_5539_);
lean_ctor_set(v___x_5541_, 1, v_trace_5311_);
lean_ctor_set(v___x_5541_, 2, v_buildTime_5312_);
lean_ctor_set_uint8(v___x_5541_, sizeof(void*)*3, v_action_5309_);
lean_ctor_set_uint8(v___x_5541_, sizeof(void*)*3 + 1, v_wantsRebuild_5310_);
v___x_5542_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5301_, v_file_5294_, v_trace_5311_, v_a_5538_, v_mtime_5540_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v___x_5541_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_a_5543_; lean_object* v_a_5544_; uint8_t v___x_5545_; uint8_t v___x_5546_; uint8_t v___x_5547_; 
v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_a_5543_);
v_a_5544_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_a_5544_);
lean_dec_ref_known(v___x_5542_, 2);
v___x_5545_ = 0;
v___x_5546_ = lean_unbox(v_a_5543_);
lean_dec(v_a_5543_);
v___x_5547_ = l_Lake_instDecidableEqOutputStatus(v___x_5546_, v___x_5545_);
if (v___x_5547_ == 0)
{
lean_object* v___x_5548_; 
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_build_5295_);
v___x_5548_ = l_Lake_computeArtifact___redArg(v_file_5294_, v_ext_5297_, v_text_5296_, v_a_5305_, v_a_5544_);
if (lean_obj_tag(v___x_5548_) == 0)
{
lean_object* v_a_5549_; lean_object* v_a_5550_; 
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
v_a_5550_ = lean_ctor_get(v___x_5548_, 1);
lean_inc(v_a_5550_);
lean_dec_ref_known(v___x_5548_, 2);
v_art_5319_ = v_a_5549_;
v___y_5320_ = v_a_5550_;
goto v___jp_5318_;
}
else
{
lean_dec_ref(v___x_5317_);
return v___x_5548_;
}
}
else
{
lean_object* v___x_5551_; 
lean_inc_ref(v___x_5317_);
v___x_5551_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5294_, v_build_5295_, v_text_5296_, v_ext_5297_, v_trace_5311_, v___x_5317_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5544_);
lean_dec_ref(v_trace_5311_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_a_5552_; lean_object* v_a_5553_; 
v_a_5552_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_a_5552_);
v_a_5553_ = lean_ctor_get(v___x_5551_, 1);
lean_inc(v_a_5553_);
lean_dec_ref_known(v___x_5551_, 2);
v_art_5319_ = v_a_5552_;
v___y_5320_ = v_a_5553_;
goto v___jp_5318_;
}
else
{
lean_dec_ref(v___x_5317_);
return v___x_5551_;
}
}
}
else
{
lean_object* v_a_5554_; lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec_ref(v___x_5317_);
lean_dec_ref(v_trace_5311_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5554_ = lean_ctor_get(v___x_5542_, 0);
v_a_5555_ = lean_ctor_get(v___x_5542_, 1);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5542_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_inc(v_a_5554_);
lean_dec(v___x_5542_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5554_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
else
{
lean_object* v_a_5563_; lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5572_; 
lean_dec_ref(v___x_5317_);
lean_del_object(v___x_5314_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_ext_5297_);
lean_dec_ref(v_build_5295_);
lean_dec_ref(v_file_5294_);
v_a_5563_ = lean_ctor_get(v___x_5346_, 0);
v_a_5564_ = lean_ctor_get(v___x_5346_, 1);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5566_ = v___x_5346_;
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_inc(v_a_5563_);
lean_dec(v___x_5346_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5568_, 0, v_a_5564_);
lean_ctor_set(v___x_5568_, 1, v_trace_5311_);
lean_ctor_set(v___x_5568_, 2, v_buildTime_5312_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*3, v_action_5309_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*3 + 1, v_wantsRebuild_5310_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 1, v___x_5568_);
v___x_5570_ = v___x_5566_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5563_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
v___jp_5318_:
{
lean_object* v_log_5321_; uint8_t v_action_5322_; uint8_t v_wantsRebuild_5323_; lean_object* v_buildTime_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5333_; 
v_log_5321_ = lean_ctor_get(v___y_5320_, 0);
v_action_5322_ = lean_ctor_get_uint8(v___y_5320_, sizeof(void*)*3);
v_wantsRebuild_5323_ = lean_ctor_get_uint8(v___y_5320_, sizeof(void*)*3 + 1);
v_buildTime_5324_ = lean_ctor_get(v___y_5320_, 2);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___y_5320_);
if (v_isSharedCheck_5333_ == 0)
{
lean_object* v_unused_5334_; 
v_unused_5334_ = lean_ctor_get(v___y_5320_, 1);
lean_dec(v_unused_5334_);
v___x_5326_ = v___y_5320_;
v_isShared_5327_ = v_isSharedCheck_5333_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_buildTime_5324_);
lean_inc(v_log_5321_);
lean_dec(v___y_5320_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5333_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5328_; lean_object* v___x_5330_; 
v___x_5328_ = l_Lake_Artifact_trace(v_art_5319_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 1, v___x_5328_);
v___x_5330_ = v___x_5326_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_log_5321_);
lean_ctor_set(v_reuseFailAlloc_5332_, 1, v___x_5328_);
lean_ctor_set(v_reuseFailAlloc_5332_, 2, v_buildTime_5324_);
lean_ctor_set_uint8(v_reuseFailAlloc_5332_, sizeof(void*)*3, v_action_5322_);
lean_ctor_set_uint8(v_reuseFailAlloc_5332_, sizeof(void*)*3 + 1, v_wantsRebuild_5323_);
v___x_5330_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
lean_object* v___x_5331_; 
v___x_5331_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5319_, v___x_5317_, v___x_5330_);
lean_dec_ref(v___x_5317_);
return v___x_5331_;
}
}
}
v___jp_5335_:
{
lean_object* v___x_5341_; lean_object* v___x_5343_; 
v___x_5341_ = l_Lake_Artifact_trace(v___y_5336_);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 2, v_buildTime_5340_);
lean_ctor_set(v___x_5314_, 1, v___x_5341_);
lean_ctor_set(v___x_5314_, 0, v_log_5337_);
v___x_5343_ = v___x_5314_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_log_5337_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5345_, 2, v_buildTime_5340_);
v___x_5343_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
lean_object* v___x_5344_; 
lean_ctor_set_uint8(v___x_5343_, sizeof(void*)*3, v_action_5338_);
lean_ctor_set_uint8(v___x_5343_, sizeof(void*)*3 + 1, v_wantsRebuild_5339_);
v___x_5344_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5336_, v___x_5317_, v___x_5343_);
lean_dec_ref(v___x_5317_);
return v___x_5344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5574_, lean_object* v_build_5575_, lean_object* v_text_5576_, lean_object* v_ext_5577_, lean_object* v_restore_5578_, lean_object* v_exe_5579_, lean_object* v_platformIndependent_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_){
_start:
{
uint8_t v_text_boxed_5588_; uint8_t v_restore_boxed_5589_; uint8_t v_exe_boxed_5590_; uint8_t v_platformIndependent_boxed_5591_; lean_object* v_res_5592_; 
v_text_boxed_5588_ = lean_unbox(v_text_5576_);
v_restore_boxed_5589_ = lean_unbox(v_restore_5578_);
v_exe_boxed_5590_ = lean_unbox(v_exe_5579_);
v_platformIndependent_boxed_5591_ = lean_unbox(v_platformIndependent_5580_);
v_res_5592_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5574_, v_build_5575_, v_text_boxed_5588_, v_ext_5577_, v_restore_boxed_5589_, v_exe_boxed_5590_, v_platformIndependent_boxed_5591_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_);
lean_dec_ref(v_a_5585_);
lean_dec(v_a_5584_);
lean_dec(v_a_5583_);
lean_dec(v_a_5582_);
return v_res_5592_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5594_, lean_object* v_build_5595_, lean_object* v_file_5596_, uint8_t v_text_5597_, lean_object* v_depInfo_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v___x_5606_; 
lean_inc_ref(v___y_5603_);
lean_inc(v___y_5602_);
lean_inc(v___y_5601_);
lean_inc(v___y_5600_);
lean_inc_ref(v___y_5599_);
v___x_5606_ = lean_apply_7(v_extraDepTrace_5594_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, lean_box(0));
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_object* v_a_5607_; lean_object* v_a_5608_; lean_object* v_log_5609_; uint8_t v_action_5610_; uint8_t v_wantsRebuild_5611_; lean_object* v_trace_5612_; lean_object* v_buildTime_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5644_; 
v_a_5607_ = lean_ctor_get(v___x_5606_, 1);
lean_inc(v_a_5607_);
v_a_5608_ = lean_ctor_get(v___x_5606_, 0);
lean_inc(v_a_5608_);
lean_dec_ref_known(v___x_5606_, 2);
v_log_5609_ = lean_ctor_get(v_a_5607_, 0);
v_action_5610_ = lean_ctor_get_uint8(v_a_5607_, sizeof(void*)*3);
v_wantsRebuild_5611_ = lean_ctor_get_uint8(v_a_5607_, sizeof(void*)*3 + 1);
v_trace_5612_ = lean_ctor_get(v_a_5607_, 1);
v_buildTime_5613_ = lean_ctor_get(v_a_5607_, 2);
v_isSharedCheck_5644_ = !lean_is_exclusive(v_a_5607_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5615_ = v_a_5607_;
v_isShared_5616_ = v_isSharedCheck_5644_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_buildTime_5613_);
lean_inc(v_trace_5612_);
lean_inc(v_log_5609_);
lean_dec(v_a_5607_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5644_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5617_ = l_Lake_BuildTrace_mix(v_trace_5612_, v_a_5608_);
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 1, v___x_5617_);
v___x_5619_ = v___x_5615_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_log_5609_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5643_, 2, v_buildTime_5613_);
lean_ctor_set_uint8(v_reuseFailAlloc_5643_, sizeof(void*)*3, v_action_5610_);
lean_ctor_set_uint8(v_reuseFailAlloc_5643_, sizeof(void*)*3 + 1, v_wantsRebuild_5611_);
v___x_5619_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
lean_object* v___x_5620_; lean_object* v___x_5621_; uint8_t v___x_5622_; lean_object* v___x_5623_; 
v___x_5620_ = lean_apply_1(v_build_5595_, v_depInfo_5598_);
v___x_5621_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5622_ = 0;
v___x_5623_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5596_, v___x_5620_, v_text_5597_, v___x_5621_, v___x_5622_, v___x_5622_, v___x_5622_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___x_5619_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v_a_5624_; lean_object* v_a_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5633_; 
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
v_a_5625_ = lean_ctor_get(v___x_5623_, 1);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5627_ = v___x_5623_;
v_isShared_5628_ = v_isSharedCheck_5633_;
goto v_resetjp_5626_;
}
else
{
lean_inc(v_a_5625_);
lean_inc(v_a_5624_);
lean_dec(v___x_5623_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5633_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v_path_5629_; lean_object* v___x_5631_; 
v_path_5629_ = lean_ctor_get(v_a_5624_, 1);
lean_inc_ref(v_path_5629_);
lean_dec(v_a_5624_);
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 0, v_path_5629_);
v___x_5631_ = v___x_5627_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_path_5629_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_a_5625_);
v___x_5631_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5630_;
}
v_reusejp_5630_:
{
return v___x_5631_;
}
}
}
else
{
lean_object* v_a_5634_; lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
v_a_5634_ = lean_ctor_get(v___x_5623_, 0);
v_a_5635_ = lean_ctor_get(v___x_5623_, 1);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5623_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_inc(v_a_5634_);
lean_dec(v___x_5623_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5634_);
lean_ctor_set(v_reuseFailAlloc_5641_, 1, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
}
}
else
{
lean_object* v_a_5645_; lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
lean_dec_ref(v___y_5599_);
lean_dec(v_depInfo_5598_);
lean_dec_ref(v_file_5596_);
lean_dec_ref(v_build_5595_);
v_a_5645_ = lean_ctor_get(v___x_5606_, 0);
v_a_5646_ = lean_ctor_get(v___x_5606_, 1);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5606_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_inc(v_a_5645_);
lean_dec(v___x_5606_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5645_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_a_5646_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5654_, lean_object* v_build_5655_, lean_object* v_file_5656_, lean_object* v_text_5657_, lean_object* v_depInfo_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
uint8_t v_text_boxed_5666_; lean_object* v_res_5667_; 
v_text_boxed_5666_ = lean_unbox(v_text_5657_);
v_res_5667_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5654_, v_build_5655_, v_file_5656_, v_text_boxed_5666_, v_depInfo_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec(v___y_5661_);
lean_dec(v___y_5660_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5668_, lean_object* v_dep_5669_, lean_object* v_build_5670_, lean_object* v_extraDepTrace_5671_, uint8_t v_text_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v___x_5680_; lean_object* v___f_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; uint8_t v___x_5684_; lean_object* v___x_5685_; 
v___x_5680_ = lean_box(v_text_5672_);
v___f_5681_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5681_, 0, v_extraDepTrace_5671_);
lean_closure_set(v___f_5681_, 1, v_build_5670_);
lean_closure_set(v___f_5681_, 2, v_file_5668_);
lean_closure_set(v___f_5681_, 3, v___x_5680_);
v___x_5682_ = l_Lake_instDataKindFilePath;
v___x_5683_ = lean_unsigned_to_nat(0u);
v___x_5684_ = 0;
v___x_5685_ = l_Lake_Job_mapM___redArg(v___x_5682_, v_dep_5669_, v___f_5681_, v___x_5683_, v___x_5684_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_);
return v___x_5685_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5686_, lean_object* v_dep_5687_, lean_object* v_build_5688_, lean_object* v_extraDepTrace_5689_, lean_object* v_text_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_){
_start:
{
uint8_t v_text_boxed_5698_; lean_object* v_res_5699_; 
v_text_boxed_5698_ = lean_unbox(v_text_5690_);
v_res_5699_ = l_Lake_buildFileAfterDep___redArg(v_file_5686_, v_dep_5687_, v_build_5688_, v_extraDepTrace_5689_, v_text_boxed_5698_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_);
lean_dec_ref(v_a_5696_);
lean_dec_ref(v_a_5695_);
lean_dec(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec(v_a_5692_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5700_, lean_object* v_file_5701_, lean_object* v_dep_5702_, lean_object* v_build_5703_, lean_object* v_extraDepTrace_5704_, uint8_t v_text_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v___x_5713_; lean_object* v___f_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; uint8_t v___x_5717_; lean_object* v___x_5718_; 
v___x_5713_ = lean_box(v_text_5705_);
v___f_5714_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5714_, 0, v_extraDepTrace_5704_);
lean_closure_set(v___f_5714_, 1, v_build_5703_);
lean_closure_set(v___f_5714_, 2, v_file_5701_);
lean_closure_set(v___f_5714_, 3, v___x_5713_);
v___x_5715_ = l_Lake_instDataKindFilePath;
v___x_5716_ = lean_unsigned_to_nat(0u);
v___x_5717_ = 0;
v___x_5718_ = l_Lake_Job_mapM___redArg(v___x_5715_, v_dep_5702_, v___f_5714_, v___x_5716_, v___x_5717_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5719_, lean_object* v_file_5720_, lean_object* v_dep_5721_, lean_object* v_build_5722_, lean_object* v_extraDepTrace_5723_, lean_object* v_text_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_){
_start:
{
uint8_t v_text_boxed_5732_; lean_object* v_res_5733_; 
v_text_boxed_5732_ = lean_unbox(v_text_5724_);
v_res_5733_ = l_Lake_buildFileAfterDep(v_00_u03b1_5719_, v_file_5720_, v_dep_5721_, v_build_5722_, v_extraDepTrace_5723_, v_text_boxed_5732_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
lean_dec_ref(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec(v_a_5727_);
lean_dec(v_a_5726_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5734_){
_start:
{
lean_object* v___x_5736_; 
v___x_5736_ = l_Lake_computeBinFileHash(v_info_5734_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v_a_5737_; lean_object* v___x_5738_; 
v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
lean_inc(v_a_5737_);
lean_dec_ref_known(v___x_5736_, 1);
v___x_5738_ = lean_io_metadata(v_info_5734_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5750_; 
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5750_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5750_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v_modified_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; uint64_t v___x_5746_; lean_object* v___x_5748_; 
v_modified_5743_ = lean_ctor_get(v_a_5739_, 1);
lean_inc_ref(v_modified_5743_);
lean_dec(v_a_5739_);
v___x_5744_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5745_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5745_, 0, v_info_5734_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
lean_ctor_set(v___x_5745_, 2, v_modified_5743_);
v___x_5746_ = lean_unbox_uint64(v_a_5737_);
lean_dec(v_a_5737_);
lean_ctor_set_uint64(v___x_5745_, sizeof(void*)*3, v___x_5746_);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 0, v___x_5745_);
v___x_5748_ = v___x_5741_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5745_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec(v_a_5737_);
lean_dec_ref(v_info_5734_);
v_a_5751_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5738_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5738_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
else
{
lean_object* v_a_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5766_; 
lean_dec_ref(v_info_5734_);
v_a_5759_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5761_ = v___x_5736_;
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_a_5759_);
lean_dec(v___x_5736_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5764_; 
if (v_isShared_5762_ == 0)
{
v___x_5764_ = v___x_5761_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5767_, lean_object* v_a_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5767_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_){
_start:
{
lean_object* v_log_5778_; uint8_t v_action_5779_; uint8_t v_wantsRebuild_5780_; lean_object* v_trace_5781_; lean_object* v_buildTime_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5802_; 
v_log_5778_ = lean_ctor_get(v___y_5776_, 0);
v_action_5779_ = lean_ctor_get_uint8(v___y_5776_, sizeof(void*)*3);
v_wantsRebuild_5780_ = lean_ctor_get_uint8(v___y_5776_, sizeof(void*)*3 + 1);
v_trace_5781_ = lean_ctor_get(v___y_5776_, 1);
v_buildTime_5782_ = lean_ctor_get(v___y_5776_, 2);
v_isSharedCheck_5802_ = !lean_is_exclusive(v___y_5776_);
if (v_isSharedCheck_5802_ == 0)
{
v___x_5784_ = v___y_5776_;
v_isShared_5785_ = v_isSharedCheck_5802_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_buildTime_5782_);
lean_inc(v_trace_5781_);
lean_inc(v_log_5778_);
lean_dec(v___y_5776_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5802_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5786_; 
lean_inc_ref(v_path_5770_);
v___x_5786_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5770_);
if (lean_obj_tag(v___x_5786_) == 0)
{
lean_object* v_a_5787_; lean_object* v___x_5789_; 
lean_dec_ref(v_trace_5781_);
v_a_5787_ = lean_ctor_get(v___x_5786_, 0);
lean_inc(v_a_5787_);
lean_dec_ref_known(v___x_5786_, 1);
if (v_isShared_5785_ == 0)
{
lean_ctor_set(v___x_5784_, 1, v_a_5787_);
v___x_5789_ = v___x_5784_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_log_5778_);
lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_a_5787_);
lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_buildTime_5782_);
lean_ctor_set_uint8(v_reuseFailAlloc_5791_, sizeof(void*)*3, v_action_5779_);
lean_ctor_set_uint8(v_reuseFailAlloc_5791_, sizeof(void*)*3 + 1, v_wantsRebuild_5780_);
v___x_5789_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5790_; 
v___x_5790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5790_, 0, v_path_5770_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
return v___x_5790_;
}
}
else
{
lean_object* v_a_5792_; lean_object* v___x_5793_; uint8_t v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5799_; 
lean_dec_ref(v_path_5770_);
v_a_5792_ = lean_ctor_get(v___x_5786_, 0);
lean_inc(v_a_5792_);
lean_dec_ref_known(v___x_5786_, 1);
v___x_5793_ = lean_io_error_to_string(v_a_5792_);
v___x_5794_ = 3;
v___x_5795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5795_, 0, v___x_5793_);
lean_ctor_set_uint8(v___x_5795_, sizeof(void*)*1, v___x_5794_);
v___x_5796_ = lean_array_get_size(v_log_5778_);
v___x_5797_ = lean_array_push(v_log_5778_, v___x_5795_);
if (v_isShared_5785_ == 0)
{
lean_ctor_set(v___x_5784_, 0, v___x_5797_);
v___x_5799_ = v___x_5784_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5797_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v_trace_5781_);
lean_ctor_set(v_reuseFailAlloc_5801_, 2, v_buildTime_5782_);
lean_ctor_set_uint8(v_reuseFailAlloc_5801_, sizeof(void*)*3, v_action_5779_);
lean_ctor_set_uint8(v_reuseFailAlloc_5801_, sizeof(void*)*3 + 1, v_wantsRebuild_5780_);
v___x_5799_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5800_; 
v___x_5800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5796_);
lean_ctor_set(v___x_5800_, 1, v___x_5799_);
return v___x_5800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
lean_dec_ref(v___y_5808_);
lean_dec(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_){
_start:
{
lean_object* v___f_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___f_5820_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5820_, 0, v_path_5813_);
v___x_5821_ = l_Lake_instDataKindFilePath;
v___x_5822_ = lean_unsigned_to_nat(0u);
v___x_5823_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5824_ = l_Lake_Job_async___redArg(v___x_5821_, v___f_5820_, v___x_5822_, v___x_5823_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_, lean_object* v_a_5830_, lean_object* v_a_5831_){
_start:
{
lean_object* v_res_5832_; 
v_res_5832_ = l_Lake_inputBinFile___redArg(v_path_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_);
lean_dec_ref(v_a_5830_);
lean_dec(v_a_5829_);
lean_dec(v_a_5828_);
lean_dec(v_a_5827_);
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_){
_start:
{
lean_object* v___x_5841_; 
v___x_5841_ = l_Lake_inputBinFile___redArg(v_path_5833_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_);
return v___x_5841_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_){
_start:
{
lean_object* v_res_5850_; 
v_res_5850_ = l_Lake_inputBinFile(v_path_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_);
lean_dec_ref(v_a_5848_);
lean_dec_ref(v_a_5847_);
lean_dec(v_a_5846_);
lean_dec(v_a_5845_);
lean_dec(v_a_5844_);
return v_res_5850_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5851_){
_start:
{
lean_object* v___x_5853_; 
v___x_5853_ = l_Lake_computeTextFileHash(v_info_5851_);
if (lean_obj_tag(v___x_5853_) == 0)
{
lean_object* v_a_5854_; lean_object* v___x_5855_; 
v_a_5854_ = lean_ctor_get(v___x_5853_, 0);
lean_inc(v_a_5854_);
lean_dec_ref_known(v___x_5853_, 1);
v___x_5855_ = lean_io_metadata(v_info_5851_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v_a_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5867_; 
v_a_5856_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5858_ = v___x_5855_;
v_isShared_5859_ = v_isSharedCheck_5867_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_a_5856_);
lean_dec(v___x_5855_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5867_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v_modified_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; uint64_t v___x_5863_; lean_object* v___x_5865_; 
v_modified_5860_ = lean_ctor_get(v_a_5856_, 1);
lean_inc_ref(v_modified_5860_);
lean_dec(v_a_5856_);
v___x_5861_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5862_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5862_, 0, v_info_5851_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
lean_ctor_set(v___x_5862_, 2, v_modified_5860_);
v___x_5863_ = lean_unbox_uint64(v_a_5854_);
lean_dec(v_a_5854_);
lean_ctor_set_uint64(v___x_5862_, sizeof(void*)*3, v___x_5863_);
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 0, v___x_5862_);
v___x_5865_ = v___x_5858_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5862_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
else
{
lean_object* v_a_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
lean_dec(v_a_5854_);
lean_dec_ref(v_info_5851_);
v_a_5868_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5875_ == 0)
{
v___x_5870_ = v___x_5855_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_a_5868_);
lean_dec(v___x_5855_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5868_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
}
else
{
lean_object* v_a_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5883_; 
lean_dec_ref(v_info_5851_);
v_a_5876_ = lean_ctor_get(v___x_5853_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5853_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5878_ = v___x_5853_;
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_a_5876_);
lean_dec(v___x_5853_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5881_; 
if (v_isShared_5879_ == 0)
{
v___x_5881_ = v___x_5878_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_a_5876_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5884_, lean_object* v_a_5885_){
_start:
{
lean_object* v_res_5886_; 
v_res_5886_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5884_);
return v_res_5886_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
lean_object* v_log_5895_; uint8_t v_action_5896_; uint8_t v_wantsRebuild_5897_; lean_object* v_trace_5898_; lean_object* v_buildTime_5899_; lean_object* v___x_5901_; uint8_t v_isShared_5902_; uint8_t v_isSharedCheck_5919_; 
v_log_5895_ = lean_ctor_get(v___y_5893_, 0);
v_action_5896_ = lean_ctor_get_uint8(v___y_5893_, sizeof(void*)*3);
v_wantsRebuild_5897_ = lean_ctor_get_uint8(v___y_5893_, sizeof(void*)*3 + 1);
v_trace_5898_ = lean_ctor_get(v___y_5893_, 1);
v_buildTime_5899_ = lean_ctor_get(v___y_5893_, 2);
v_isSharedCheck_5919_ = !lean_is_exclusive(v___y_5893_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5901_ = v___y_5893_;
v_isShared_5902_ = v_isSharedCheck_5919_;
goto v_resetjp_5900_;
}
else
{
lean_inc(v_buildTime_5899_);
lean_inc(v_trace_5898_);
lean_inc(v_log_5895_);
lean_dec(v___y_5893_);
v___x_5901_ = lean_box(0);
v_isShared_5902_ = v_isSharedCheck_5919_;
goto v_resetjp_5900_;
}
v_resetjp_5900_:
{
lean_object* v___x_5903_; 
lean_inc_ref(v_path_5887_);
v___x_5903_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5887_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; lean_object* v___x_5906_; 
lean_dec_ref(v_trace_5898_);
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
lean_inc(v_a_5904_);
lean_dec_ref_known(v___x_5903_, 1);
if (v_isShared_5902_ == 0)
{
lean_ctor_set(v___x_5901_, 1, v_a_5904_);
v___x_5906_ = v___x_5901_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_log_5895_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v_a_5904_);
lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_buildTime_5899_);
lean_ctor_set_uint8(v_reuseFailAlloc_5908_, sizeof(void*)*3, v_action_5896_);
lean_ctor_set_uint8(v_reuseFailAlloc_5908_, sizeof(void*)*3 + 1, v_wantsRebuild_5897_);
v___x_5906_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___x_5907_; 
v___x_5907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5907_, 0, v_path_5887_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
return v___x_5907_;
}
}
else
{
lean_object* v_a_5909_; lean_object* v___x_5910_; uint8_t v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5916_; 
lean_dec_ref(v_path_5887_);
v_a_5909_ = lean_ctor_get(v___x_5903_, 0);
lean_inc(v_a_5909_);
lean_dec_ref_known(v___x_5903_, 1);
v___x_5910_ = lean_io_error_to_string(v_a_5909_);
v___x_5911_ = 3;
v___x_5912_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set_uint8(v___x_5912_, sizeof(void*)*1, v___x_5911_);
v___x_5913_ = lean_array_get_size(v_log_5895_);
v___x_5914_ = lean_array_push(v_log_5895_, v___x_5912_);
if (v_isShared_5902_ == 0)
{
lean_ctor_set(v___x_5901_, 0, v___x_5914_);
v___x_5916_ = v___x_5901_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5914_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_trace_5898_);
lean_ctor_set(v_reuseFailAlloc_5918_, 2, v_buildTime_5899_);
lean_ctor_set_uint8(v_reuseFailAlloc_5918_, sizeof(void*)*3, v_action_5896_);
lean_ctor_set_uint8(v_reuseFailAlloc_5918_, sizeof(void*)*3 + 1, v_wantsRebuild_5897_);
v___x_5916_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
lean_object* v___x_5917_; 
v___x_5917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5913_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
return v___x_5917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
lean_object* v_res_5928_; 
v_res_5928_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec(v___y_5923_);
lean_dec(v___y_5922_);
lean_dec_ref(v___y_5921_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_){
_start:
{
lean_object* v___f_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___f_5936_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5936_, 0, v_path_5929_);
v___x_5937_ = l_Lake_instDataKindFilePath;
v___x_5938_ = lean_unsigned_to_nat(0u);
v___x_5939_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5940_ = l_Lake_Job_async___redArg(v___x_5937_, v___f_5936_, v___x_5938_, v___x_5939_, v_a_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_);
return v___x_5940_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_){
_start:
{
lean_object* v_res_5948_; 
v_res_5948_ = l_Lake_inputTextFile___redArg(v_path_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
lean_dec_ref(v_a_5946_);
lean_dec(v_a_5945_);
lean_dec(v_a_5944_);
lean_dec(v_a_5943_);
return v_res_5948_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_){
_start:
{
lean_object* v___x_5957_; 
v___x_5957_ = l_Lake_inputTextFile___redArg(v_path_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l_Lake_inputTextFile(v_path_5958_, v_a_5959_, v_a_5960_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
lean_dec_ref(v_a_5964_);
lean_dec_ref(v_a_5963_);
lean_dec(v_a_5962_);
lean_dec(v_a_5961_);
lean_dec(v_a_5960_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5967_, uint8_t v_text_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_){
_start:
{
if (v_text_5968_ == 0)
{
lean_object* v___x_5975_; 
v___x_5975_ = l_Lake_inputBinFile___redArg(v_path_5967_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
return v___x_5975_;
}
else
{
lean_object* v___x_5976_; 
v___x_5976_ = l_Lake_inputTextFile___redArg(v_path_5967_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
return v___x_5976_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5977_, lean_object* v_text_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
uint8_t v_text_boxed_5985_; lean_object* v_res_5986_; 
v_text_boxed_5985_ = lean_unbox(v_text_5978_);
v_res_5986_ = l_Lake_inputFile___redArg(v_path_5977_, v_text_boxed_5985_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec(v_a_5981_);
lean_dec(v_a_5980_);
return v_res_5986_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5987_, uint8_t v_text_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_){
_start:
{
if (v_text_5988_ == 0)
{
lean_object* v___x_5996_; 
v___x_5996_ = l_Lake_inputBinFile___redArg(v_path_5987_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
return v___x_5996_;
}
else
{
lean_object* v___x_5997_; 
v___x_5997_ = l_Lake_inputTextFile___redArg(v_path_5987_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
return v___x_5997_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5998_, lean_object* v_text_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_){
_start:
{
uint8_t v_text_boxed_6007_; lean_object* v_res_6008_; 
v_text_boxed_6007_ = lean_unbox(v_text_5999_);
v_res_6008_ = l_Lake_inputFile(v_path_5998_, v_text_boxed_6007_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_);
lean_dec_ref(v_a_6005_);
lean_dec_ref(v_a_6004_);
lean_dec(v_a_6003_);
lean_dec(v_a_6002_);
lean_dec(v_a_6001_);
return v_res_6008_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6009_){
_start:
{
uint8_t v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6011_ = 1;
v___x_6012_ = lean_box(v___x_6011_);
v___x_6013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
return v___x_6013_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6014_, lean_object* v___y_6015_){
_start:
{
lean_object* v_res_6016_; 
v_res_6016_ = l_Lake_inputDir___lam__0(v_x_6014_);
lean_dec_ref(v_x_6014_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6017_, lean_object* v_as_6018_, size_t v_i_6019_, size_t v_stop_6020_, lean_object* v_b_6021_, lean_object* v___y_6022_){
_start:
{
lean_object* v_a_6025_; lean_object* v_a_6026_; uint8_t v___x_6030_; 
v___x_6030_ = lean_usize_dec_eq(v_i_6019_, v_stop_6020_);
if (v___x_6030_ == 0)
{
lean_object* v___x_6031_; uint8_t v___x_6032_; 
v___x_6031_ = lean_array_uget_borrowed(v_as_6018_, v_i_6019_);
v___x_6032_ = l_System_FilePath_isDir(v___x_6031_);
if (v___x_6032_ == 0)
{
lean_object* v___x_6033_; uint8_t v___x_6034_; 
lean_inc_ref(v_filter_6017_);
lean_inc(v___x_6031_);
v___x_6033_ = lean_apply_1(v_filter_6017_, v___x_6031_);
v___x_6034_ = lean_unbox(v___x_6033_);
if (v___x_6034_ == 0)
{
v_a_6025_ = v_b_6021_;
v_a_6026_ = v___y_6022_;
goto v___jp_6024_;
}
else
{
lean_object* v___x_6035_; 
lean_inc(v___x_6031_);
v___x_6035_ = lean_array_push(v_b_6021_, v___x_6031_);
v_a_6025_ = v___x_6035_;
v_a_6026_ = v___y_6022_;
goto v___jp_6024_;
}
}
else
{
v_a_6025_ = v_b_6021_;
v_a_6026_ = v___y_6022_;
goto v___jp_6024_;
}
}
else
{
lean_object* v___x_6036_; 
lean_dec_ref(v_filter_6017_);
v___x_6036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6036_, 0, v_b_6021_);
lean_ctor_set(v___x_6036_, 1, v___y_6022_);
return v___x_6036_;
}
v___jp_6024_:
{
size_t v___x_6027_; size_t v___x_6028_; 
v___x_6027_ = ((size_t)1ULL);
v___x_6028_ = lean_usize_add(v_i_6019_, v___x_6027_);
v_i_6019_ = v___x_6028_;
v_b_6021_ = v_a_6025_;
v___y_6022_ = v_a_6026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6037_, lean_object* v_as_6038_, lean_object* v_i_6039_, lean_object* v_stop_6040_, lean_object* v_b_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_){
_start:
{
size_t v_i_boxed_6044_; size_t v_stop_boxed_6045_; lean_object* v_res_6046_; 
v_i_boxed_6044_ = lean_unbox_usize(v_i_6039_);
lean_dec(v_i_6039_);
v_stop_boxed_6045_ = lean_unbox_usize(v_stop_6040_);
lean_dec(v_stop_6040_);
v_res_6046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6037_, v_as_6038_, v_i_boxed_6044_, v_stop_boxed_6045_, v_b_6041_, v___y_6042_);
lean_dec_ref(v_as_6038_);
return v_res_6046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6047_, lean_object* v_pivot_6048_, lean_object* v_as_6049_, lean_object* v_i_6050_, lean_object* v_k_6051_){
_start:
{
uint8_t v___x_6052_; 
v___x_6052_ = lean_nat_dec_lt(v_k_6051_, v_hi_6047_);
if (v___x_6052_ == 0)
{
lean_object* v___x_6053_; lean_object* v___x_6054_; 
lean_dec(v_k_6051_);
v___x_6053_ = lean_array_fswap(v_as_6049_, v_i_6050_, v_hi_6047_);
v___x_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6054_, 0, v_i_6050_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
return v___x_6054_;
}
else
{
lean_object* v___x_6055_; uint8_t v___x_6056_; 
v___x_6055_ = lean_array_fget_borrowed(v_as_6049_, v_k_6051_);
v___x_6056_ = lean_string_dec_lt(v___x_6055_, v_pivot_6048_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6057_ = lean_unsigned_to_nat(1u);
v___x_6058_ = lean_nat_add(v_k_6051_, v___x_6057_);
lean_dec(v_k_6051_);
v_k_6051_ = v___x_6058_;
goto _start;
}
else
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6060_ = lean_array_fswap(v_as_6049_, v_i_6050_, v_k_6051_);
v___x_6061_ = lean_unsigned_to_nat(1u);
v___x_6062_ = lean_nat_add(v_i_6050_, v___x_6061_);
lean_dec(v_i_6050_);
v___x_6063_ = lean_nat_add(v_k_6051_, v___x_6061_);
lean_dec(v_k_6051_);
v_as_6049_ = v___x_6060_;
v_i_6050_ = v___x_6062_;
v_k_6051_ = v___x_6063_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6065_, lean_object* v_pivot_6066_, lean_object* v_as_6067_, lean_object* v_i_6068_, lean_object* v_k_6069_){
_start:
{
lean_object* v_res_6070_; 
v_res_6070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6065_, v_pivot_6066_, v_as_6067_, v_i_6068_, v_k_6069_);
lean_dec_ref(v_pivot_6066_);
lean_dec(v_hi_6065_);
return v_res_6070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6071_, lean_object* v_as_6072_, lean_object* v_lo_6073_, lean_object* v_hi_6074_){
_start:
{
lean_object* v___y_6076_; uint8_t v___x_6086_; 
v___x_6086_ = lean_nat_dec_lt(v_lo_6073_, v_hi_6074_);
if (v___x_6086_ == 0)
{
lean_dec(v_lo_6073_);
return v_as_6072_;
}
else
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v_mid_6089_; lean_object* v___y_6091_; lean_object* v___y_6097_; lean_object* v___x_6102_; lean_object* v___x_6103_; uint8_t v___x_6104_; 
v___x_6087_ = lean_nat_add(v_lo_6073_, v_hi_6074_);
v___x_6088_ = lean_unsigned_to_nat(1u);
v_mid_6089_ = lean_nat_shiftr(v___x_6087_, v___x_6088_);
lean_dec(v___x_6087_);
v___x_6102_ = lean_array_fget_borrowed(v_as_6072_, v_mid_6089_);
v___x_6103_ = lean_array_fget_borrowed(v_as_6072_, v_lo_6073_);
v___x_6104_ = lean_string_dec_lt(v___x_6102_, v___x_6103_);
if (v___x_6104_ == 0)
{
v___y_6097_ = v_as_6072_;
goto v___jp_6096_;
}
else
{
lean_object* v___x_6105_; 
v___x_6105_ = lean_array_fswap(v_as_6072_, v_lo_6073_, v_mid_6089_);
v___y_6097_ = v___x_6105_;
goto v___jp_6096_;
}
v___jp_6090_:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; uint8_t v___x_6094_; 
v___x_6092_ = lean_array_fget_borrowed(v___y_6091_, v_mid_6089_);
v___x_6093_ = lean_array_fget_borrowed(v___y_6091_, v_hi_6074_);
v___x_6094_ = lean_string_dec_lt(v___x_6092_, v___x_6093_);
if (v___x_6094_ == 0)
{
lean_dec(v_mid_6089_);
v___y_6076_ = v___y_6091_;
goto v___jp_6075_;
}
else
{
lean_object* v___x_6095_; 
v___x_6095_ = lean_array_fswap(v___y_6091_, v_mid_6089_, v_hi_6074_);
lean_dec(v_mid_6089_);
v___y_6076_ = v___x_6095_;
goto v___jp_6075_;
}
}
v___jp_6096_:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; uint8_t v___x_6100_; 
v___x_6098_ = lean_array_fget_borrowed(v___y_6097_, v_hi_6074_);
v___x_6099_ = lean_array_fget_borrowed(v___y_6097_, v_lo_6073_);
v___x_6100_ = lean_string_dec_lt(v___x_6098_, v___x_6099_);
if (v___x_6100_ == 0)
{
v___y_6091_ = v___y_6097_;
goto v___jp_6090_;
}
else
{
lean_object* v___x_6101_; 
v___x_6101_ = lean_array_fswap(v___y_6097_, v_lo_6073_, v_hi_6074_);
v___y_6091_ = v___x_6101_;
goto v___jp_6090_;
}
}
}
v___jp_6075_:
{
lean_object* v_pivot_6077_; lean_object* v___x_6078_; lean_object* v_fst_6079_; lean_object* v_snd_6080_; uint8_t v___x_6081_; 
v_pivot_6077_ = lean_array_fget(v___y_6076_, v_hi_6074_);
lean_inc_n(v_lo_6073_, 2);
v___x_6078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6074_, v_pivot_6077_, v___y_6076_, v_lo_6073_, v_lo_6073_);
lean_dec(v_pivot_6077_);
v_fst_6079_ = lean_ctor_get(v___x_6078_, 0);
lean_inc(v_fst_6079_);
v_snd_6080_ = lean_ctor_get(v___x_6078_, 1);
lean_inc(v_snd_6080_);
lean_dec_ref(v___x_6078_);
v___x_6081_ = lean_nat_dec_le(v_hi_6074_, v_fst_6079_);
if (v___x_6081_ == 0)
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6071_, v_snd_6080_, v_lo_6073_, v_fst_6079_);
v___x_6083_ = lean_unsigned_to_nat(1u);
v___x_6084_ = lean_nat_add(v_fst_6079_, v___x_6083_);
lean_dec(v_fst_6079_);
v_as_6072_ = v___x_6082_;
v_lo_6073_ = v___x_6084_;
goto _start;
}
else
{
lean_dec(v_fst_6079_);
lean_dec(v_lo_6073_);
return v_snd_6080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6106_, lean_object* v_as_6107_, lean_object* v_lo_6108_, lean_object* v_hi_6109_){
_start:
{
lean_object* v_res_6110_; 
v_res_6110_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6106_, v_as_6107_, v_lo_6108_, v_hi_6109_);
lean_dec(v_hi_6109_);
lean_dec(v_n_6106_);
return v_res_6110_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6113_, lean_object* v___f_6114_, lean_object* v_filter_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6128_; lean_object* v___y_6129_; lean_object* v___y_6130_; lean_object* v___y_6131_; lean_object* v___y_6132_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; lean_object* v_log_6141_; uint8_t v_action_6142_; uint8_t v_wantsRebuild_6143_; lean_object* v_trace_6144_; lean_object* v_buildTime_6145_; lean_object* v___x_6146_; 
v_log_6141_ = lean_ctor_get(v___y_6121_, 0);
v_action_6142_ = lean_ctor_get_uint8(v___y_6121_, sizeof(void*)*3);
v_wantsRebuild_6143_ = lean_ctor_get_uint8(v___y_6121_, sizeof(void*)*3 + 1);
v_trace_6144_ = lean_ctor_get(v___y_6121_, 1);
v_buildTime_6145_ = lean_ctor_get(v___y_6121_, 2);
v___x_6146_ = l_System_FilePath_walkDir(v_path_6113_, v___f_6114_);
if (lean_obj_tag(v___x_6146_) == 0)
{
lean_object* v_a_6147_; lean_object* v___x_6148_; lean_object* v_a_6150_; lean_object* v_a_6151_; lean_object* v___y_6158_; lean_object* v___x_6161_; lean_object* v___x_6162_; uint8_t v___x_6163_; 
v_a_6147_ = lean_ctor_get(v___x_6146_, 0);
lean_inc(v_a_6147_);
lean_dec_ref_known(v___x_6146_, 1);
v___x_6148_ = lean_unsigned_to_nat(0u);
v___x_6161_ = lean_array_get_size(v_a_6147_);
v___x_6162_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6163_ = lean_nat_dec_lt(v___x_6148_, v___x_6161_);
if (v___x_6163_ == 0)
{
lean_dec(v_a_6147_);
lean_dec_ref(v_filter_6115_);
v_a_6150_ = v___x_6162_;
v_a_6151_ = v___y_6121_;
goto v___jp_6149_;
}
else
{
uint8_t v___x_6164_; 
v___x_6164_ = lean_nat_dec_le(v___x_6161_, v___x_6161_);
if (v___x_6164_ == 0)
{
if (v___x_6163_ == 0)
{
lean_dec(v_a_6147_);
lean_dec_ref(v_filter_6115_);
v_a_6150_ = v___x_6162_;
v_a_6151_ = v___y_6121_;
goto v___jp_6149_;
}
else
{
size_t v___x_6165_; size_t v___x_6166_; lean_object* v___x_6167_; 
v___x_6165_ = ((size_t)0ULL);
v___x_6166_ = lean_usize_of_nat(v___x_6161_);
v___x_6167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6115_, v_a_6147_, v___x_6165_, v___x_6166_, v___x_6162_, v___y_6121_);
lean_dec(v_a_6147_);
v___y_6158_ = v___x_6167_;
goto v___jp_6157_;
}
}
else
{
size_t v___x_6168_; size_t v___x_6169_; lean_object* v___x_6170_; 
v___x_6168_ = ((size_t)0ULL);
v___x_6169_ = lean_usize_of_nat(v___x_6161_);
v___x_6170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6115_, v_a_6147_, v___x_6168_, v___x_6169_, v___x_6162_, v___y_6121_);
lean_dec(v_a_6147_);
v___y_6158_ = v___x_6170_;
goto v___jp_6157_;
}
}
v___jp_6149_:
{
lean_object* v___x_6152_; uint8_t v___x_6153_; 
v___x_6152_ = lean_array_get_size(v_a_6150_);
v___x_6153_ = lean_nat_dec_eq(v___x_6152_, v___x_6148_);
if (v___x_6153_ == 0)
{
lean_object* v___x_6154_; lean_object* v___x_6155_; uint8_t v___x_6156_; 
v___x_6154_ = lean_unsigned_to_nat(1u);
v___x_6155_ = lean_nat_sub(v___x_6152_, v___x_6154_);
v___x_6156_ = lean_nat_dec_le(v___x_6148_, v___x_6155_);
if (v___x_6156_ == 0)
{
lean_inc(v___x_6155_);
v___y_6135_ = v___x_6155_;
v___y_6136_ = v_a_6151_;
v___y_6137_ = v___x_6152_;
v___y_6138_ = v_a_6150_;
v___y_6139_ = v___x_6155_;
goto v___jp_6134_;
}
else
{
v___y_6135_ = v___x_6155_;
v___y_6136_ = v_a_6151_;
v___y_6137_ = v___x_6152_;
v___y_6138_ = v_a_6150_;
v___y_6139_ = v___x_6148_;
goto v___jp_6134_;
}
}
else
{
v___y_6124_ = v_a_6151_;
v___y_6125_ = v_a_6150_;
goto v___jp_6123_;
}
}
v___jp_6157_:
{
if (lean_obj_tag(v___y_6158_) == 0)
{
lean_object* v_a_6159_; lean_object* v_a_6160_; 
v_a_6159_ = lean_ctor_get(v___y_6158_, 0);
lean_inc(v_a_6159_);
v_a_6160_ = lean_ctor_get(v___y_6158_, 1);
lean_inc(v_a_6160_);
lean_dec_ref_known(v___y_6158_, 2);
v_a_6150_ = v_a_6159_;
v_a_6151_ = v_a_6160_;
goto v___jp_6149_;
}
else
{
return v___y_6158_;
}
}
}
else
{
lean_object* v___x_6172_; uint8_t v_isShared_6173_; uint8_t v_isSharedCheck_6184_; 
lean_inc(v_buildTime_6145_);
lean_inc_ref(v_trace_6144_);
lean_inc_ref(v_log_6141_);
lean_dec_ref(v_filter_6115_);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___y_6121_);
if (v_isSharedCheck_6184_ == 0)
{
lean_object* v_unused_6185_; lean_object* v_unused_6186_; lean_object* v_unused_6187_; 
v_unused_6185_ = lean_ctor_get(v___y_6121_, 2);
lean_dec(v_unused_6185_);
v_unused_6186_ = lean_ctor_get(v___y_6121_, 1);
lean_dec(v_unused_6186_);
v_unused_6187_ = lean_ctor_get(v___y_6121_, 0);
lean_dec(v_unused_6187_);
v___x_6172_ = v___y_6121_;
v_isShared_6173_ = v_isSharedCheck_6184_;
goto v_resetjp_6171_;
}
else
{
lean_dec(v___y_6121_);
v___x_6172_ = lean_box(0);
v_isShared_6173_ = v_isSharedCheck_6184_;
goto v_resetjp_6171_;
}
v_resetjp_6171_:
{
lean_object* v_a_6174_; lean_object* v___x_6175_; uint8_t v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6181_; 
v_a_6174_ = lean_ctor_get(v___x_6146_, 0);
lean_inc(v_a_6174_);
lean_dec_ref_known(v___x_6146_, 1);
v___x_6175_ = lean_io_error_to_string(v_a_6174_);
v___x_6176_ = 3;
v___x_6177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6177_, 0, v___x_6175_);
lean_ctor_set_uint8(v___x_6177_, sizeof(void*)*1, v___x_6176_);
v___x_6178_ = lean_array_get_size(v_log_6141_);
v___x_6179_ = lean_array_push(v_log_6141_, v___x_6177_);
if (v_isShared_6173_ == 0)
{
lean_ctor_set(v___x_6172_, 0, v___x_6179_);
v___x_6181_ = v___x_6172_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v___x_6179_);
lean_ctor_set(v_reuseFailAlloc_6183_, 1, v_trace_6144_);
lean_ctor_set(v_reuseFailAlloc_6183_, 2, v_buildTime_6145_);
lean_ctor_set_uint8(v_reuseFailAlloc_6183_, sizeof(void*)*3, v_action_6142_);
lean_ctor_set_uint8(v_reuseFailAlloc_6183_, sizeof(void*)*3 + 1, v_wantsRebuild_6143_);
v___x_6181_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
lean_object* v___x_6182_; 
v___x_6182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6178_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
return v___x_6182_;
}
}
}
v___jp_6123_:
{
lean_object* v___x_6126_; 
v___x_6126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___y_6125_);
lean_ctor_set(v___x_6126_, 1, v___y_6124_);
return v___x_6126_;
}
v___jp_6127_:
{
lean_object* v___x_6133_; 
v___x_6133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6130_, v___y_6131_, v___y_6129_, v___y_6132_);
lean_dec(v___y_6132_);
lean_dec(v___y_6130_);
v___y_6124_ = v___y_6128_;
v___y_6125_ = v___x_6133_;
goto v___jp_6123_;
}
v___jp_6134_:
{
uint8_t v___x_6140_; 
v___x_6140_ = lean_nat_dec_le(v___y_6139_, v___y_6135_);
if (v___x_6140_ == 0)
{
lean_dec(v___y_6135_);
lean_inc(v___y_6139_);
v___y_6128_ = v___y_6136_;
v___y_6129_ = v___y_6139_;
v___y_6130_ = v___y_6137_;
v___y_6131_ = v___y_6138_;
v___y_6132_ = v___y_6139_;
goto v___jp_6127_;
}
else
{
v___y_6128_ = v___y_6136_;
v___y_6129_ = v___y_6139_;
v___y_6130_ = v___y_6137_;
v___y_6131_ = v___y_6138_;
v___y_6132_ = v___y_6135_;
goto v___jp_6127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6188_, lean_object* v___f_6189_, lean_object* v_filter_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l_Lake_inputDir___lam__1(v_path_6188_, v___f_6189_, v_filter_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6199_, size_t v_sz_6200_, size_t v_i_6201_, lean_object* v_bs_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_){
_start:
{
uint8_t v___x_6210_; 
v___x_6210_ = lean_usize_dec_lt(v_i_6201_, v_sz_6200_);
if (v___x_6210_ == 0)
{
lean_object* v___x_6211_; 
lean_dec_ref(v___y_6203_);
v___x_6211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6211_, 0, v_bs_6202_);
lean_ctor_set(v___x_6211_, 1, v___y_6208_);
return v___x_6211_;
}
else
{
lean_object* v_v_6212_; lean_object* v___x_6213_; lean_object* v_bs_x27_6214_; lean_object* v___y_6216_; 
v_v_6212_ = lean_array_uget(v_bs_6202_, v_i_6201_);
v___x_6213_ = lean_unsigned_to_nat(0u);
v_bs_x27_6214_ = lean_array_uset(v_bs_6202_, v_i_6201_, v___x_6213_);
if (v_text_6199_ == 0)
{
lean_object* v___x_6221_; 
lean_inc_ref(v___y_6203_);
v___x_6221_ = l_Lake_inputBinFile___redArg(v_v_6212_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_);
v___y_6216_ = v___x_6221_;
goto v___jp_6215_;
}
else
{
lean_object* v___x_6222_; 
lean_inc_ref(v___y_6203_);
v___x_6222_ = l_Lake_inputTextFile___redArg(v_v_6212_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_);
v___y_6216_ = v___x_6222_;
goto v___jp_6215_;
}
v___jp_6215_:
{
size_t v___x_6217_; size_t v___x_6218_; lean_object* v___x_6219_; 
v___x_6217_ = ((size_t)1ULL);
v___x_6218_ = lean_usize_add(v_i_6201_, v___x_6217_);
v___x_6219_ = lean_array_uset(v_bs_x27_6214_, v_i_6201_, v___y_6216_);
v_i_6201_ = v___x_6218_;
v_bs_6202_ = v___x_6219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6223_, lean_object* v_sz_6224_, lean_object* v_i_6225_, lean_object* v_bs_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
uint8_t v_text_boxed_6234_; size_t v_sz_boxed_6235_; size_t v_i_boxed_6236_; lean_object* v_res_6237_; 
v_text_boxed_6234_ = lean_unbox(v_text_6223_);
v_sz_boxed_6235_ = lean_unbox_usize(v_sz_6224_);
lean_dec(v_sz_6224_);
v_i_boxed_6236_ = lean_unbox_usize(v_i_6225_);
lean_dec(v_i_6225_);
v_res_6237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6234_, v_sz_boxed_6235_, v_i_boxed_6236_, v_bs_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec(v___y_6229_);
lean_dec(v___y_6228_);
return v_res_6237_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6238_, lean_object* v_path_6239_, lean_object* v_ps_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
size_t v_sz_6248_; size_t v___x_6249_; lean_object* v___x_6250_; 
v_sz_6248_ = lean_array_size(v_ps_6240_);
v___x_6249_ = ((size_t)0ULL);
v___x_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6238_, v_sz_6248_, v___x_6249_, v_ps_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
if (lean_obj_tag(v___x_6250_) == 0)
{
lean_object* v_a_6251_; lean_object* v_a_6252_; lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6260_; 
v_a_6251_ = lean_ctor_get(v___x_6250_, 0);
v_a_6252_ = lean_ctor_get(v___x_6250_, 1);
v_isSharedCheck_6260_ = !lean_is_exclusive(v___x_6250_);
if (v_isSharedCheck_6260_ == 0)
{
v___x_6254_ = v___x_6250_;
v_isShared_6255_ = v_isSharedCheck_6260_;
goto v_resetjp_6253_;
}
else
{
lean_inc(v_a_6252_);
lean_inc(v_a_6251_);
lean_dec(v___x_6250_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6260_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
lean_object* v___x_6256_; lean_object* v___x_6258_; 
v___x_6256_ = l_Lake_Job_collectArray___redArg(v_a_6251_, v_path_6239_);
lean_dec(v_a_6251_);
if (v_isShared_6255_ == 0)
{
lean_ctor_set(v___x_6254_, 0, v___x_6256_);
v___x_6258_ = v___x_6254_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v___x_6256_);
lean_ctor_set(v_reuseFailAlloc_6259_, 1, v_a_6252_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
}
else
{
lean_object* v_a_6261_; lean_object* v_a_6262_; lean_object* v___x_6264_; uint8_t v_isShared_6265_; uint8_t v_isSharedCheck_6269_; 
lean_dec_ref(v_path_6239_);
v_a_6261_ = lean_ctor_get(v___x_6250_, 0);
v_a_6262_ = lean_ctor_get(v___x_6250_, 1);
v_isSharedCheck_6269_ = !lean_is_exclusive(v___x_6250_);
if (v_isSharedCheck_6269_ == 0)
{
v___x_6264_ = v___x_6250_;
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
else
{
lean_inc(v_a_6262_);
lean_inc(v_a_6261_);
lean_dec(v___x_6250_);
v___x_6264_ = lean_box(0);
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
v_resetjp_6263_:
{
lean_object* v___x_6267_; 
if (v_isShared_6265_ == 0)
{
v___x_6267_ = v___x_6264_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6268_; 
v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6261_);
lean_ctor_set(v_reuseFailAlloc_6268_, 1, v_a_6262_);
v___x_6267_ = v_reuseFailAlloc_6268_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
return v___x_6267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6270_, lean_object* v_path_6271_, lean_object* v_ps_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_){
_start:
{
uint8_t v_text_boxed_6280_; lean_object* v_res_6281_; 
v_text_boxed_6280_ = lean_unbox(v_text_6270_);
v_res_6281_ = l_Lake_inputDir___lam__2(v_text_boxed_6280_, v_path_6271_, v_ps_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
lean_dec_ref(v___y_6277_);
lean_dec(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec(v___y_6274_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6283_, uint8_t v_text_6284_, lean_object* v_filter_6285_, lean_object* v_a_6286_, lean_object* v_a_6287_, lean_object* v_a_6288_, lean_object* v_a_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_){
_start:
{
lean_object* v___f_6293_; lean_object* v___f_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___f_6300_; uint8_t v___x_6301_; lean_object* v___x_6302_; 
v___f_6293_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6283_);
v___f_6294_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6294_, 0, v_path_6283_);
lean_closure_set(v___f_6294_, 1, v___f_6293_);
lean_closure_set(v___f_6294_, 2, v_filter_6285_);
v___x_6295_ = lean_box(0);
v___x_6296_ = lean_unsigned_to_nat(0u);
v___x_6297_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6286_);
v___x_6298_ = l_Lake_Job_async___redArg(v___x_6295_, v___f_6294_, v___x_6296_, v___x_6297_, v_a_6286_, v_a_6287_, v_a_6288_, v_a_6289_, v_a_6290_);
v___x_6299_ = lean_box(v_text_6284_);
v___f_6300_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6300_, 0, v___x_6299_);
lean_closure_set(v___f_6300_, 1, v_path_6283_);
v___x_6301_ = 0;
v___x_6302_ = l_Lake_Job_bindM___redArg(v___x_6295_, v___x_6298_, v___f_6300_, v___x_6296_, v___x_6301_, v_a_6286_, v_a_6287_, v_a_6288_, v_a_6289_, v_a_6290_, v_a_6291_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6303_, lean_object* v_text_6304_, lean_object* v_filter_6305_, lean_object* v_a_6306_, lean_object* v_a_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_){
_start:
{
uint8_t v_text_boxed_6313_; lean_object* v_res_6314_; 
v_text_boxed_6313_ = lean_unbox(v_text_6304_);
v_res_6314_ = l_Lake_inputDir(v_path_6303_, v_text_boxed_6313_, v_filter_6305_, v_a_6306_, v_a_6307_, v_a_6308_, v_a_6309_, v_a_6310_, v_a_6311_);
lean_dec_ref(v_a_6311_);
lean_dec_ref(v_a_6310_);
lean_dec(v_a_6309_);
lean_dec(v_a_6308_);
lean_dec(v_a_6307_);
return v_res_6314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6315_, lean_object* v_as_6316_, lean_object* v_lo_6317_, lean_object* v_hi_6318_, lean_object* v_w_6319_, lean_object* v_hlo_6320_, lean_object* v_hhi_6321_){
_start:
{
lean_object* v___x_6322_; 
v___x_6322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6315_, v_as_6316_, v_lo_6317_, v_hi_6318_);
return v___x_6322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6323_, lean_object* v_as_6324_, lean_object* v_lo_6325_, lean_object* v_hi_6326_, lean_object* v_w_6327_, lean_object* v_hlo_6328_, lean_object* v_hhi_6329_){
_start:
{
lean_object* v_res_6330_; 
v_res_6330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6323_, v_as_6324_, v_lo_6325_, v_hi_6326_, v_w_6327_, v_hlo_6328_, v_hhi_6329_);
lean_dec(v_hi_6326_);
lean_dec(v_n_6323_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6331_, lean_object* v_as_6332_, size_t v_i_6333_, size_t v_stop_6334_, lean_object* v_b_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_){
_start:
{
lean_object* v___x_6343_; 
v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6331_, v_as_6332_, v_i_6333_, v_stop_6334_, v_b_6335_, v___y_6341_);
return v___x_6343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6344_, lean_object* v_as_6345_, lean_object* v_i_6346_, lean_object* v_stop_6347_, lean_object* v_b_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_){
_start:
{
size_t v_i_boxed_6356_; size_t v_stop_boxed_6357_; lean_object* v_res_6358_; 
v_i_boxed_6356_ = lean_unbox_usize(v_i_6346_);
lean_dec(v_i_6346_);
v_stop_boxed_6357_ = lean_unbox_usize(v_stop_6347_);
lean_dec(v_stop_6347_);
v_res_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6344_, v_as_6345_, v_i_boxed_6356_, v_stop_boxed_6357_, v_b_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
lean_dec_ref(v___y_6353_);
lean_dec(v___y_6352_);
lean_dec(v___y_6351_);
lean_dec(v___y_6350_);
lean_dec_ref(v___y_6349_);
lean_dec_ref(v_as_6345_);
return v_res_6358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6359_, lean_object* v_lo_6360_, lean_object* v_hi_6361_, lean_object* v_hhi_6362_, lean_object* v_pivot_6363_, lean_object* v_as_6364_, lean_object* v_i_6365_, lean_object* v_k_6366_, lean_object* v_ilo_6367_, lean_object* v_ik_6368_, lean_object* v_w_6369_){
_start:
{
lean_object* v___x_6370_; 
v___x_6370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6361_, v_pivot_6363_, v_as_6364_, v_i_6365_, v_k_6366_);
return v___x_6370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6371_, lean_object* v_lo_6372_, lean_object* v_hi_6373_, lean_object* v_hhi_6374_, lean_object* v_pivot_6375_, lean_object* v_as_6376_, lean_object* v_i_6377_, lean_object* v_k_6378_, lean_object* v_ilo_6379_, lean_object* v_ik_6380_, lean_object* v_w_6381_){
_start:
{
lean_object* v_res_6382_; 
v_res_6382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6371_, v_lo_6372_, v_hi_6373_, v_hhi_6374_, v_pivot_6375_, v_as_6376_, v_i_6377_, v_k_6378_, v_ilo_6379_, v_ik_6380_, v_w_6381_);
lean_dec_ref(v_pivot_6375_);
lean_dec(v_hi_6373_);
lean_dec(v_lo_6372_);
lean_dec(v_n_6371_);
return v_res_6382_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6383_, lean_object* v_t_6384_){
_start:
{
uint64_t v___x_6385_; uint64_t v___x_6386_; uint64_t v___x_6387_; uint64_t v___x_6388_; 
v___x_6385_ = l_Lake_Hash_nil;
v___x_6386_ = lean_string_hash(v_t_6384_);
v___x_6387_ = lean_uint64_mix_hash(v___x_6385_, v___x_6386_);
v___x_6388_ = lean_uint64_mix_hash(v_ts_6383_, v___x_6387_);
return v___x_6388_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6389_, lean_object* v_t_6390_){
_start:
{
uint64_t v_ts_boxed_6391_; uint64_t v_res_6392_; lean_object* v_r_6393_; 
v_ts_boxed_6391_ = lean_unbox_uint64(v_ts_6389_);
lean_dec_ref(v_ts_6389_);
v_res_6392_ = l_Lake_buildO___lam__0(v_ts_boxed_6391_, v_t_6390_);
lean_dec_ref(v_t_6390_);
v_r_6393_ = lean_box_uint64(v_res_6392_);
return v_r_6393_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6394_, lean_object* v_srcFile_6395_, lean_object* v___x_6396_, lean_object* v_compiler_6397_, lean_object* v___y_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_){
_start:
{
lean_object* v_log_6405_; uint8_t v_action_6406_; uint8_t v_wantsRebuild_6407_; lean_object* v_trace_6408_; lean_object* v_buildTime_6409_; lean_object* v___x_6411_; uint8_t v_isShared_6412_; uint8_t v_isSharedCheck_6438_; 
v_log_6405_ = lean_ctor_get(v___y_6403_, 0);
v_action_6406_ = lean_ctor_get_uint8(v___y_6403_, sizeof(void*)*3);
v_wantsRebuild_6407_ = lean_ctor_get_uint8(v___y_6403_, sizeof(void*)*3 + 1);
v_trace_6408_ = lean_ctor_get(v___y_6403_, 1);
v_buildTime_6409_ = lean_ctor_get(v___y_6403_, 2);
v_isSharedCheck_6438_ = !lean_is_exclusive(v___y_6403_);
if (v_isSharedCheck_6438_ == 0)
{
v___x_6411_ = v___y_6403_;
v_isShared_6412_ = v_isSharedCheck_6438_;
goto v_resetjp_6410_;
}
else
{
lean_inc(v_buildTime_6409_);
lean_inc(v_trace_6408_);
lean_inc(v_log_6405_);
lean_dec(v___y_6403_);
v___x_6411_ = lean_box(0);
v_isShared_6412_ = v_isSharedCheck_6438_;
goto v_resetjp_6410_;
}
v_resetjp_6410_:
{
lean_object* v___x_6413_; 
v___x_6413_ = l_Lake_compileO(v_oFile_6394_, v_srcFile_6395_, v___x_6396_, v_compiler_6397_, v_log_6405_);
if (lean_obj_tag(v___x_6413_) == 0)
{
lean_object* v_a_6414_; lean_object* v_a_6415_; lean_object* v___x_6417_; uint8_t v_isShared_6418_; uint8_t v_isSharedCheck_6425_; 
v_a_6414_ = lean_ctor_get(v___x_6413_, 0);
v_a_6415_ = lean_ctor_get(v___x_6413_, 1);
v_isSharedCheck_6425_ = !lean_is_exclusive(v___x_6413_);
if (v_isSharedCheck_6425_ == 0)
{
v___x_6417_ = v___x_6413_;
v_isShared_6418_ = v_isSharedCheck_6425_;
goto v_resetjp_6416_;
}
else
{
lean_inc(v_a_6415_);
lean_inc(v_a_6414_);
lean_dec(v___x_6413_);
v___x_6417_ = lean_box(0);
v_isShared_6418_ = v_isSharedCheck_6425_;
goto v_resetjp_6416_;
}
v_resetjp_6416_:
{
lean_object* v___x_6420_; 
if (v_isShared_6412_ == 0)
{
lean_ctor_set(v___x_6411_, 0, v_a_6415_);
v___x_6420_ = v___x_6411_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6424_; 
v_reuseFailAlloc_6424_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6424_, 0, v_a_6415_);
lean_ctor_set(v_reuseFailAlloc_6424_, 1, v_trace_6408_);
lean_ctor_set(v_reuseFailAlloc_6424_, 2, v_buildTime_6409_);
lean_ctor_set_uint8(v_reuseFailAlloc_6424_, sizeof(void*)*3, v_action_6406_);
lean_ctor_set_uint8(v_reuseFailAlloc_6424_, sizeof(void*)*3 + 1, v_wantsRebuild_6407_);
v___x_6420_ = v_reuseFailAlloc_6424_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
lean_object* v___x_6422_; 
if (v_isShared_6418_ == 0)
{
lean_ctor_set(v___x_6417_, 1, v___x_6420_);
v___x_6422_ = v___x_6417_;
goto v_reusejp_6421_;
}
else
{
lean_object* v_reuseFailAlloc_6423_; 
v_reuseFailAlloc_6423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6423_, 0, v_a_6414_);
lean_ctor_set(v_reuseFailAlloc_6423_, 1, v___x_6420_);
v___x_6422_ = v_reuseFailAlloc_6423_;
goto v_reusejp_6421_;
}
v_reusejp_6421_:
{
return v___x_6422_;
}
}
}
}
else
{
lean_object* v_a_6426_; lean_object* v_a_6427_; lean_object* v___x_6429_; uint8_t v_isShared_6430_; uint8_t v_isSharedCheck_6437_; 
v_a_6426_ = lean_ctor_get(v___x_6413_, 0);
v_a_6427_ = lean_ctor_get(v___x_6413_, 1);
v_isSharedCheck_6437_ = !lean_is_exclusive(v___x_6413_);
if (v_isSharedCheck_6437_ == 0)
{
v___x_6429_ = v___x_6413_;
v_isShared_6430_ = v_isSharedCheck_6437_;
goto v_resetjp_6428_;
}
else
{
lean_inc(v_a_6427_);
lean_inc(v_a_6426_);
lean_dec(v___x_6413_);
v___x_6429_ = lean_box(0);
v_isShared_6430_ = v_isSharedCheck_6437_;
goto v_resetjp_6428_;
}
v_resetjp_6428_:
{
lean_object* v___x_6432_; 
if (v_isShared_6412_ == 0)
{
lean_ctor_set(v___x_6411_, 0, v_a_6427_);
v___x_6432_ = v___x_6411_;
goto v_reusejp_6431_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_a_6427_);
lean_ctor_set(v_reuseFailAlloc_6436_, 1, v_trace_6408_);
lean_ctor_set(v_reuseFailAlloc_6436_, 2, v_buildTime_6409_);
lean_ctor_set_uint8(v_reuseFailAlloc_6436_, sizeof(void*)*3, v_action_6406_);
lean_ctor_set_uint8(v_reuseFailAlloc_6436_, sizeof(void*)*3 + 1, v_wantsRebuild_6407_);
v___x_6432_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6431_;
}
v_reusejp_6431_:
{
lean_object* v___x_6434_; 
if (v_isShared_6430_ == 0)
{
lean_ctor_set(v___x_6429_, 1, v___x_6432_);
v___x_6434_ = v___x_6429_;
goto v_reusejp_6433_;
}
else
{
lean_object* v_reuseFailAlloc_6435_; 
v_reuseFailAlloc_6435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6426_);
lean_ctor_set(v_reuseFailAlloc_6435_, 1, v___x_6432_);
v___x_6434_ = v_reuseFailAlloc_6435_;
goto v_reusejp_6433_;
}
v_reusejp_6433_:
{
return v___x_6434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6439_, lean_object* v_srcFile_6440_, lean_object* v___x_6441_, lean_object* v_compiler_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_){
_start:
{
lean_object* v_res_6450_; 
v_res_6450_ = l_Lake_buildO___lam__1(v_oFile_6439_, v_srcFile_6440_, v___x_6441_, v_compiler_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec_ref(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec(v___y_6444_);
lean_dec_ref(v___y_6443_);
lean_dec_ref(v___x_6441_);
return v_res_6450_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6454_; lean_object* v___x_6455_; 
v___x_6454_ = l_Lake_Hash_nil;
v___x_6455_ = lean_box_uint64(v___x_6454_);
return v___x_6455_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6456_, lean_object* v___f_6457_, lean_object* v_extraDepTrace_6458_, lean_object* v_weakArgs_6459_, lean_object* v_oFile_6460_, lean_object* v_compiler_6461_, lean_object* v___x_6462_, lean_object* v___f_6463_, lean_object* v_srcFile_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
lean_object* v_log_6472_; uint8_t v_action_6473_; uint8_t v_wantsRebuild_6474_; lean_object* v_trace_6475_; lean_object* v_buildTime_6476_; lean_object* v___x_6478_; uint8_t v_isShared_6479_; uint8_t v_isSharedCheck_6561_; 
v_log_6472_ = lean_ctor_get(v___y_6470_, 0);
v_action_6473_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*3);
v_wantsRebuild_6474_ = lean_ctor_get_uint8(v___y_6470_, sizeof(void*)*3 + 1);
v_trace_6475_ = lean_ctor_get(v___y_6470_, 1);
v_buildTime_6476_ = lean_ctor_get(v___y_6470_, 2);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___y_6470_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6478_ = v___y_6470_;
v_isShared_6479_ = v_isSharedCheck_6561_;
goto v_resetjp_6477_;
}
else
{
lean_inc(v_buildTime_6476_);
lean_inc(v_trace_6475_);
lean_inc(v_log_6472_);
lean_dec(v___y_6470_);
v___x_6478_ = lean_box(0);
v_isShared_6479_ = v_isSharedCheck_6561_;
goto v_resetjp_6477_;
}
v_resetjp_6477_:
{
lean_object* v___x_6480_; lean_object* v___x_6481_; uint64_t v___y_6483_; uint64_t v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; uint8_t v___x_6549_; 
v___x_6480_ = l_Lake_platformTrace;
v___x_6481_ = l_Lake_BuildTrace_mix(v_trace_6475_, v___x_6480_);
v___x_6546_ = l_Lake_Hash_nil;
v___x_6547_ = lean_unsigned_to_nat(0u);
v___x_6548_ = lean_array_get_size(v_traceArgs_6456_);
v___x_6549_ = lean_nat_dec_lt(v___x_6547_, v___x_6548_);
if (v___x_6549_ == 0)
{
lean_dec_ref(v___f_6463_);
lean_dec_ref(v___x_6462_);
v___y_6483_ = v___x_6546_;
goto v___jp_6482_;
}
else
{
uint8_t v___x_6550_; 
v___x_6550_ = lean_nat_dec_le(v___x_6548_, v___x_6548_);
if (v___x_6550_ == 0)
{
if (v___x_6549_ == 0)
{
lean_dec_ref(v___f_6463_);
lean_dec_ref(v___x_6462_);
v___y_6483_ = v___x_6546_;
goto v___jp_6482_;
}
else
{
size_t v___x_6551_; size_t v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; uint64_t v___x_6555_; 
v___x_6551_ = ((size_t)0ULL);
v___x_6552_ = lean_usize_of_nat(v___x_6548_);
v___x_6553_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6456_);
v___x_6554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6462_, v___f_6463_, v_traceArgs_6456_, v___x_6551_, v___x_6552_, v___x_6553_);
v___x_6555_ = lean_unbox_uint64(v___x_6554_);
lean_dec(v___x_6554_);
v___y_6483_ = v___x_6555_;
goto v___jp_6482_;
}
}
else
{
size_t v___x_6556_; size_t v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; uint64_t v___x_6560_; 
v___x_6556_ = ((size_t)0ULL);
v___x_6557_ = lean_usize_of_nat(v___x_6548_);
v___x_6558_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6456_);
v___x_6559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6462_, v___f_6463_, v_traceArgs_6456_, v___x_6556_, v___x_6557_, v___x_6558_);
v___x_6560_ = lean_unbox_uint64(v___x_6559_);
lean_dec(v___x_6559_);
v___y_6483_ = v___x_6560_;
goto v___jp_6482_;
}
}
v___jp_6482_:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6495_; 
v___x_6484_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6485_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6456_);
v___x_6486_ = lean_array_to_list(v_traceArgs_6456_);
v___x_6487_ = l_List_toString___redArg(v___f_6457_, v___x_6486_);
v___x_6488_ = lean_string_append(v___x_6485_, v___x_6487_);
lean_dec_ref(v___x_6487_);
v___x_6489_ = lean_string_append(v___x_6484_, v___x_6488_);
lean_dec_ref(v___x_6488_);
v___x_6490_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6491_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6492_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6492_, 0, v___x_6489_);
lean_ctor_set(v___x_6492_, 1, v___x_6490_);
lean_ctor_set(v___x_6492_, 2, v___x_6491_);
lean_ctor_set_uint64(v___x_6492_, sizeof(void*)*3, v___y_6483_);
v___x_6493_ = l_Lake_BuildTrace_mix(v___x_6481_, v___x_6492_);
if (v_isShared_6479_ == 0)
{
lean_ctor_set(v___x_6478_, 1, v___x_6493_);
v___x_6495_ = v___x_6478_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_log_6472_);
lean_ctor_set(v_reuseFailAlloc_6545_, 1, v___x_6493_);
lean_ctor_set(v_reuseFailAlloc_6545_, 2, v_buildTime_6476_);
lean_ctor_set_uint8(v_reuseFailAlloc_6545_, sizeof(void*)*3, v_action_6473_);
lean_ctor_set_uint8(v_reuseFailAlloc_6545_, sizeof(void*)*3 + 1, v_wantsRebuild_6474_);
v___x_6495_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
lean_object* v___x_6496_; 
lean_inc_ref(v___y_6469_);
lean_inc(v___y_6468_);
lean_inc(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
v___x_6496_ = lean_apply_7(v_extraDepTrace_6458_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___x_6495_, lean_box(0));
if (lean_obj_tag(v___x_6496_) == 0)
{
lean_object* v_a_6497_; lean_object* v_a_6498_; lean_object* v_log_6499_; uint8_t v_action_6500_; uint8_t v_wantsRebuild_6501_; lean_object* v_trace_6502_; lean_object* v_buildTime_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6535_; 
v_a_6497_ = lean_ctor_get(v___x_6496_, 1);
lean_inc(v_a_6497_);
v_a_6498_ = lean_ctor_get(v___x_6496_, 0);
lean_inc(v_a_6498_);
lean_dec_ref_known(v___x_6496_, 2);
v_log_6499_ = lean_ctor_get(v_a_6497_, 0);
v_action_6500_ = lean_ctor_get_uint8(v_a_6497_, sizeof(void*)*3);
v_wantsRebuild_6501_ = lean_ctor_get_uint8(v_a_6497_, sizeof(void*)*3 + 1);
v_trace_6502_ = lean_ctor_get(v_a_6497_, 1);
v_buildTime_6503_ = lean_ctor_get(v_a_6497_, 2);
v_isSharedCheck_6535_ = !lean_is_exclusive(v_a_6497_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6505_ = v_a_6497_;
v_isShared_6506_ = v_isSharedCheck_6535_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_buildTime_6503_);
lean_inc(v_trace_6502_);
lean_inc(v_log_6499_);
lean_dec(v_a_6497_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6535_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v___x_6507_; lean_object* v___x_6509_; 
v___x_6507_ = l_Lake_BuildTrace_mix(v_trace_6502_, v_a_6498_);
if (v_isShared_6506_ == 0)
{
lean_ctor_set(v___x_6505_, 1, v___x_6507_);
v___x_6509_ = v___x_6505_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_log_6499_);
lean_ctor_set(v_reuseFailAlloc_6534_, 1, v___x_6507_);
lean_ctor_set(v_reuseFailAlloc_6534_, 2, v_buildTime_6503_);
lean_ctor_set_uint8(v_reuseFailAlloc_6534_, sizeof(void*)*3, v_action_6500_);
lean_ctor_set_uint8(v_reuseFailAlloc_6534_, sizeof(void*)*3 + 1, v_wantsRebuild_6501_);
v___x_6509_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
lean_object* v___x_6510_; lean_object* v___f_6511_; uint8_t v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; 
v___x_6510_ = l_Array_append___redArg(v_weakArgs_6459_, v_traceArgs_6456_);
lean_dec_ref(v_traceArgs_6456_);
lean_inc_ref(v_oFile_6460_);
v___f_6511_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6511_, 0, v_oFile_6460_);
lean_closure_set(v___f_6511_, 1, v_srcFile_6464_);
lean_closure_set(v___f_6511_, 2, v___x_6510_);
lean_closure_set(v___f_6511_, 3, v_compiler_6461_);
v___x_6512_ = 0;
v___x_6513_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6514_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6460_, v___f_6511_, v___x_6512_, v___x_6513_, v___x_6512_, v___x_6512_, v___x_6512_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___x_6509_);
if (lean_obj_tag(v___x_6514_) == 0)
{
lean_object* v_a_6515_; lean_object* v_a_6516_; lean_object* v___x_6518_; uint8_t v_isShared_6519_; uint8_t v_isSharedCheck_6524_; 
v_a_6515_ = lean_ctor_get(v___x_6514_, 0);
v_a_6516_ = lean_ctor_get(v___x_6514_, 1);
v_isSharedCheck_6524_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6524_ == 0)
{
v___x_6518_ = v___x_6514_;
v_isShared_6519_ = v_isSharedCheck_6524_;
goto v_resetjp_6517_;
}
else
{
lean_inc(v_a_6516_);
lean_inc(v_a_6515_);
lean_dec(v___x_6514_);
v___x_6518_ = lean_box(0);
v_isShared_6519_ = v_isSharedCheck_6524_;
goto v_resetjp_6517_;
}
v_resetjp_6517_:
{
lean_object* v_path_6520_; lean_object* v___x_6522_; 
v_path_6520_ = lean_ctor_get(v_a_6515_, 1);
lean_inc_ref(v_path_6520_);
lean_dec(v_a_6515_);
if (v_isShared_6519_ == 0)
{
lean_ctor_set(v___x_6518_, 0, v_path_6520_);
v___x_6522_ = v___x_6518_;
goto v_reusejp_6521_;
}
else
{
lean_object* v_reuseFailAlloc_6523_; 
v_reuseFailAlloc_6523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_path_6520_);
lean_ctor_set(v_reuseFailAlloc_6523_, 1, v_a_6516_);
v___x_6522_ = v_reuseFailAlloc_6523_;
goto v_reusejp_6521_;
}
v_reusejp_6521_:
{
return v___x_6522_;
}
}
}
else
{
lean_object* v_a_6525_; lean_object* v_a_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6533_; 
v_a_6525_ = lean_ctor_get(v___x_6514_, 0);
v_a_6526_ = lean_ctor_get(v___x_6514_, 1);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6528_ = v___x_6514_;
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_a_6526_);
lean_inc(v_a_6525_);
lean_dec(v___x_6514_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v___x_6531_; 
if (v_isShared_6529_ == 0)
{
v___x_6531_ = v___x_6528_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6525_);
lean_ctor_set(v_reuseFailAlloc_6532_, 1, v_a_6526_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
return v___x_6531_;
}
}
}
}
}
}
else
{
lean_object* v_a_6536_; lean_object* v_a_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6544_; 
lean_dec_ref(v___y_6465_);
lean_dec_ref(v_srcFile_6464_);
lean_dec_ref(v_compiler_6461_);
lean_dec_ref(v_oFile_6460_);
lean_dec_ref(v_weakArgs_6459_);
lean_dec_ref(v_traceArgs_6456_);
v_a_6536_ = lean_ctor_get(v___x_6496_, 0);
v_a_6537_ = lean_ctor_get(v___x_6496_, 1);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6496_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6539_ = v___x_6496_;
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_a_6537_);
lean_inc(v_a_6536_);
lean_dec(v___x_6496_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
lean_object* v___x_6542_; 
if (v_isShared_6540_ == 0)
{
v___x_6542_ = v___x_6539_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6536_);
lean_ctor_set(v_reuseFailAlloc_6543_, 1, v_a_6537_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
return v___x_6542_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6562_, lean_object* v___f_6563_, lean_object* v_extraDepTrace_6564_, lean_object* v_weakArgs_6565_, lean_object* v_oFile_6566_, lean_object* v_compiler_6567_, lean_object* v___x_6568_, lean_object* v___f_6569_, lean_object* v_srcFile_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_){
_start:
{
lean_object* v_res_6578_; 
v_res_6578_ = l_Lake_buildO___lam__2(v_traceArgs_6562_, v___f_6563_, v_extraDepTrace_6564_, v_weakArgs_6565_, v_oFile_6566_, v_compiler_6567_, v___x_6568_, v___f_6569_, v_srcFile_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec(v___y_6574_);
lean_dec(v___y_6573_);
lean_dec(v___y_6572_);
return v_res_6578_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6581_, lean_object* v_srcJob_6582_, lean_object* v_weakArgs_6583_, lean_object* v_traceArgs_6584_, lean_object* v_compiler_6585_, lean_object* v_extraDepTrace_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v___f_6594_; lean_object* v___x_6595_; lean_object* v___f_6596_; lean_object* v___x_6597_; lean_object* v___f_6598_; lean_object* v___x_6599_; uint8_t v___x_6600_; lean_object* v___x_6601_; 
v___f_6594_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6595_ = l_Lake_instDataKindFilePath;
v___f_6596_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6597_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6598_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6598_, 0, v_traceArgs_6584_);
lean_closure_set(v___f_6598_, 1, v___f_6596_);
lean_closure_set(v___f_6598_, 2, v_extraDepTrace_6586_);
lean_closure_set(v___f_6598_, 3, v_weakArgs_6583_);
lean_closure_set(v___f_6598_, 4, v_oFile_6581_);
lean_closure_set(v___f_6598_, 5, v_compiler_6585_);
lean_closure_set(v___f_6598_, 6, v___x_6597_);
lean_closure_set(v___f_6598_, 7, v___f_6594_);
v___x_6599_ = lean_unsigned_to_nat(0u);
v___x_6600_ = 0;
v___x_6601_ = l_Lake_Job_mapM___redArg(v___x_6595_, v_srcJob_6582_, v___f_6598_, v___x_6599_, v___x_6600_, v_a_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
return v___x_6601_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6602_, lean_object* v_srcJob_6603_, lean_object* v_weakArgs_6604_, lean_object* v_traceArgs_6605_, lean_object* v_compiler_6606_, lean_object* v_extraDepTrace_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l_Lake_buildO(v_oFile_6602_, v_srcJob_6603_, v_weakArgs_6604_, v_traceArgs_6605_, v_compiler_6606_, v_extraDepTrace_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_);
lean_dec_ref(v_a_6613_);
lean_dec_ref(v_a_6612_);
lean_dec(v_a_6611_);
lean_dec(v_a_6610_);
lean_dec(v_a_6609_);
return v_res_6615_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; 
v___x_6617_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6618_ = lean_unsigned_to_nat(2u);
v___x_6619_ = lean_mk_empty_array_with_capacity(v___x_6618_);
v___x_6620_ = lean_array_push(v___x_6619_, v___x_6617_);
return v___x_6620_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6621_, lean_object* v_traceArgs_6622_, lean_object* v_oFile_6623_, lean_object* v_srcFile_6624_, lean_object* v_leanIncludeDir_x3f_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v_toContext_6633_; lean_object* v_lakeEnv_6634_; lean_object* v_log_6635_; uint8_t v_action_6636_; uint8_t v_wantsRebuild_6637_; lean_object* v_trace_6638_; lean_object* v_buildTime_6639_; lean_object* v___x_6641_; uint8_t v_isShared_6642_; uint8_t v_isSharedCheck_6680_; 
v_toContext_6633_ = lean_ctor_get(v___y_6630_, 1);
v_lakeEnv_6634_ = lean_ctor_get(v_toContext_6633_, 0);
v_log_6635_ = lean_ctor_get(v___y_6631_, 0);
v_action_6636_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3);
v_wantsRebuild_6637_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3 + 1);
v_trace_6638_ = lean_ctor_get(v___y_6631_, 1);
v_buildTime_6639_ = lean_ctor_get(v___y_6631_, 2);
v_isSharedCheck_6680_ = !lean_is_exclusive(v___y_6631_);
if (v_isSharedCheck_6680_ == 0)
{
v___x_6641_ = v___y_6631_;
v_isShared_6642_ = v_isSharedCheck_6680_;
goto v_resetjp_6640_;
}
else
{
lean_inc(v_buildTime_6639_);
lean_inc(v_trace_6638_);
lean_inc(v_log_6635_);
lean_dec(v___y_6631_);
v___x_6641_ = lean_box(0);
v_isShared_6642_ = v_isSharedCheck_6680_;
goto v_resetjp_6640_;
}
v_resetjp_6640_:
{
lean_object* v_lean_6643_; lean_object* v___y_6645_; 
v_lean_6643_ = lean_ctor_get(v_lakeEnv_6634_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6625_) == 0)
{
lean_object* v_includeDir_6678_; 
v_includeDir_6678_ = lean_ctor_get(v_lean_6643_, 4);
lean_inc_ref(v_includeDir_6678_);
v___y_6645_ = v_includeDir_6678_;
goto v___jp_6644_;
}
else
{
lean_object* v_val_6679_; 
v_val_6679_ = lean_ctor_get(v_leanIncludeDir_x3f_6625_, 0);
lean_inc(v_val_6679_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6625_, 1);
v___y_6645_ = v_val_6679_;
goto v___jp_6644_;
}
v___jp_6644_:
{
lean_object* v_cc_6646_; lean_object* v_ccFlags_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; 
v_cc_6646_ = lean_ctor_get(v_lean_6643_, 14);
v_ccFlags_6647_ = lean_ctor_get(v_lean_6643_, 18);
v___x_6648_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6649_ = lean_array_push(v___x_6648_, v___y_6645_);
v___x_6650_ = l_Array_append___redArg(v___x_6649_, v_ccFlags_6647_);
v___x_6651_ = l_Array_append___redArg(v___x_6650_, v_weakArgs_6621_);
v___x_6652_ = l_Array_append___redArg(v___x_6651_, v_traceArgs_6622_);
lean_inc_ref(v_cc_6646_);
v___x_6653_ = l_Lake_compileO(v_oFile_6623_, v_srcFile_6624_, v___x_6652_, v_cc_6646_, v_log_6635_);
lean_dec_ref(v___x_6652_);
if (lean_obj_tag(v___x_6653_) == 0)
{
lean_object* v_a_6654_; lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6665_; 
v_a_6654_ = lean_ctor_get(v___x_6653_, 0);
v_a_6655_ = lean_ctor_get(v___x_6653_, 1);
v_isSharedCheck_6665_ = !lean_is_exclusive(v___x_6653_);
if (v_isSharedCheck_6665_ == 0)
{
v___x_6657_ = v___x_6653_;
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_inc(v_a_6654_);
lean_dec(v___x_6653_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6642_ == 0)
{
lean_ctor_set(v___x_6641_, 0, v_a_6655_);
v___x_6660_ = v___x_6641_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6664_; 
v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6655_);
lean_ctor_set(v_reuseFailAlloc_6664_, 1, v_trace_6638_);
lean_ctor_set(v_reuseFailAlloc_6664_, 2, v_buildTime_6639_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3, v_action_6636_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3 + 1, v_wantsRebuild_6637_);
v___x_6660_ = v_reuseFailAlloc_6664_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
lean_object* v___x_6662_; 
if (v_isShared_6658_ == 0)
{
lean_ctor_set(v___x_6657_, 1, v___x_6660_);
v___x_6662_ = v___x_6657_;
goto v_reusejp_6661_;
}
else
{
lean_object* v_reuseFailAlloc_6663_; 
v_reuseFailAlloc_6663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6663_, 0, v_a_6654_);
lean_ctor_set(v_reuseFailAlloc_6663_, 1, v___x_6660_);
v___x_6662_ = v_reuseFailAlloc_6663_;
goto v_reusejp_6661_;
}
v_reusejp_6661_:
{
return v___x_6662_;
}
}
}
}
else
{
lean_object* v_a_6666_; lean_object* v_a_6667_; lean_object* v___x_6669_; uint8_t v_isShared_6670_; uint8_t v_isSharedCheck_6677_; 
v_a_6666_ = lean_ctor_get(v___x_6653_, 0);
v_a_6667_ = lean_ctor_get(v___x_6653_, 1);
v_isSharedCheck_6677_ = !lean_is_exclusive(v___x_6653_);
if (v_isSharedCheck_6677_ == 0)
{
v___x_6669_ = v___x_6653_;
v_isShared_6670_ = v_isSharedCheck_6677_;
goto v_resetjp_6668_;
}
else
{
lean_inc(v_a_6667_);
lean_inc(v_a_6666_);
lean_dec(v___x_6653_);
v___x_6669_ = lean_box(0);
v_isShared_6670_ = v_isSharedCheck_6677_;
goto v_resetjp_6668_;
}
v_resetjp_6668_:
{
lean_object* v___x_6672_; 
if (v_isShared_6642_ == 0)
{
lean_ctor_set(v___x_6641_, 0, v_a_6667_);
v___x_6672_ = v___x_6641_;
goto v_reusejp_6671_;
}
else
{
lean_object* v_reuseFailAlloc_6676_; 
v_reuseFailAlloc_6676_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6676_, 0, v_a_6667_);
lean_ctor_set(v_reuseFailAlloc_6676_, 1, v_trace_6638_);
lean_ctor_set(v_reuseFailAlloc_6676_, 2, v_buildTime_6639_);
lean_ctor_set_uint8(v_reuseFailAlloc_6676_, sizeof(void*)*3, v_action_6636_);
lean_ctor_set_uint8(v_reuseFailAlloc_6676_, sizeof(void*)*3 + 1, v_wantsRebuild_6637_);
v___x_6672_ = v_reuseFailAlloc_6676_;
goto v_reusejp_6671_;
}
v_reusejp_6671_:
{
lean_object* v___x_6674_; 
if (v_isShared_6670_ == 0)
{
lean_ctor_set(v___x_6669_, 1, v___x_6672_);
v___x_6674_ = v___x_6669_;
goto v_reusejp_6673_;
}
else
{
lean_object* v_reuseFailAlloc_6675_; 
v_reuseFailAlloc_6675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6675_, 0, v_a_6666_);
lean_ctor_set(v_reuseFailAlloc_6675_, 1, v___x_6672_);
v___x_6674_ = v_reuseFailAlloc_6675_;
goto v_reusejp_6673_;
}
v_reusejp_6673_:
{
return v___x_6674_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6681_, lean_object* v_traceArgs_6682_, lean_object* v_oFile_6683_, lean_object* v_srcFile_6684_, lean_object* v_leanIncludeDir_x3f_6685_, lean_object* v___y_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_){
_start:
{
lean_object* v_res_6693_; 
v_res_6693_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6681_, v_traceArgs_6682_, v_oFile_6683_, v_srcFile_6684_, v_leanIncludeDir_x3f_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_);
lean_dec_ref(v___y_6690_);
lean_dec(v___y_6689_);
lean_dec(v___y_6688_);
lean_dec(v___y_6687_);
lean_dec_ref(v___y_6686_);
lean_dec_ref(v_traceArgs_6682_);
lean_dec_ref(v_weakArgs_6681_);
return v_res_6693_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6694_, size_t v_i_6695_, size_t v_stop_6696_, uint64_t v_b_6697_){
_start:
{
uint8_t v___x_6698_; 
v___x_6698_ = lean_usize_dec_eq(v_i_6695_, v_stop_6696_);
if (v___x_6698_ == 0)
{
lean_object* v___x_6699_; uint64_t v___x_6700_; uint64_t v___x_6701_; uint64_t v___x_6702_; uint64_t v___x_6703_; size_t v___x_6704_; size_t v___x_6705_; 
v___x_6699_ = lean_array_uget_borrowed(v_as_6694_, v_i_6695_);
v___x_6700_ = l_Lake_Hash_nil;
v___x_6701_ = lean_string_hash(v___x_6699_);
v___x_6702_ = lean_uint64_mix_hash(v___x_6700_, v___x_6701_);
v___x_6703_ = lean_uint64_mix_hash(v_b_6697_, v___x_6702_);
v___x_6704_ = ((size_t)1ULL);
v___x_6705_ = lean_usize_add(v_i_6695_, v___x_6704_);
v_i_6695_ = v___x_6705_;
v_b_6697_ = v___x_6703_;
goto _start;
}
else
{
return v_b_6697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6707_, lean_object* v_i_6708_, lean_object* v_stop_6709_, lean_object* v_b_6710_){
_start:
{
size_t v_i_boxed_6711_; size_t v_stop_boxed_6712_; uint64_t v_b_boxed_6713_; uint64_t v_res_6714_; lean_object* v_r_6715_; 
v_i_boxed_6711_ = lean_unbox_usize(v_i_6708_);
lean_dec(v_i_6708_);
v_stop_boxed_6712_ = lean_unbox_usize(v_stop_6709_);
lean_dec(v_stop_6709_);
v_b_boxed_6713_ = lean_unbox_uint64(v_b_6710_);
lean_dec_ref(v_b_6710_);
v_res_6714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6707_, v_i_boxed_6711_, v_stop_boxed_6712_, v_b_boxed_6713_);
lean_dec_ref(v_as_6707_);
v_r_6715_ = lean_box_uint64(v_res_6714_);
return v_r_6715_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6717_, lean_object* v_x_6718_){
_start:
{
if (lean_obj_tag(v_x_6718_) == 0)
{
return v_x_6717_;
}
else
{
lean_object* v_head_6719_; lean_object* v_tail_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; 
v_head_6719_ = lean_ctor_get(v_x_6718_, 0);
v_tail_6720_ = lean_ctor_get(v_x_6718_, 1);
v___x_6721_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6722_ = lean_string_append(v_x_6717_, v___x_6721_);
v___x_6723_ = lean_string_append(v___x_6722_, v_head_6719_);
v_x_6717_ = v___x_6723_;
v_x_6718_ = v_tail_6720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6725_, lean_object* v_x_6726_){
_start:
{
lean_object* v_res_6727_; 
v_res_6727_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6725_, v_x_6726_);
lean_dec(v_x_6726_);
return v_res_6727_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6731_){
_start:
{
if (lean_obj_tag(v_x_6731_) == 0)
{
lean_object* v___x_6732_; 
v___x_6732_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6732_;
}
else
{
lean_object* v_tail_6733_; 
v_tail_6733_ = lean_ctor_get(v_x_6731_, 1);
if (lean_obj_tag(v_tail_6733_) == 0)
{
lean_object* v_head_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; 
v_head_6734_ = lean_ctor_get(v_x_6731_, 0);
v___x_6735_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6736_ = lean_string_append(v___x_6735_, v_head_6734_);
v___x_6737_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6738_ = lean_string_append(v___x_6736_, v___x_6737_);
return v___x_6738_;
}
else
{
lean_object* v_head_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; uint32_t v___x_6743_; lean_object* v___x_6744_; 
v_head_6739_ = lean_ctor_get(v_x_6731_, 0);
v___x_6740_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6741_ = lean_string_append(v___x_6740_, v_head_6739_);
v___x_6742_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6741_, v_tail_6733_);
v___x_6743_ = 93;
v___x_6744_ = lean_string_push(v___x_6742_, v___x_6743_);
return v___x_6744_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6745_){
_start:
{
lean_object* v_res_6746_; 
v_res_6746_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6745_);
lean_dec(v_x_6745_);
return v_res_6746_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6747_, lean_object* v_traceArgs_6748_, lean_object* v_oFile_6749_, lean_object* v_leanIncludeDir_x3f_6750_, lean_object* v_srcFile_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_){
_start:
{
lean_object* v_log_6759_; uint8_t v_action_6760_; uint8_t v_wantsRebuild_6761_; lean_object* v_trace_6762_; lean_object* v_buildTime_6763_; lean_object* v___x_6765_; uint8_t v_isShared_6766_; uint8_t v_isSharedCheck_6820_; 
v_log_6759_ = lean_ctor_get(v___y_6757_, 0);
v_action_6760_ = lean_ctor_get_uint8(v___y_6757_, sizeof(void*)*3);
v_wantsRebuild_6761_ = lean_ctor_get_uint8(v___y_6757_, sizeof(void*)*3 + 1);
v_trace_6762_ = lean_ctor_get(v___y_6757_, 1);
v_buildTime_6763_ = lean_ctor_get(v___y_6757_, 2);
v_isSharedCheck_6820_ = !lean_is_exclusive(v___y_6757_);
if (v_isSharedCheck_6820_ == 0)
{
v___x_6765_ = v___y_6757_;
v_isShared_6766_ = v_isSharedCheck_6820_;
goto v_resetjp_6764_;
}
else
{
lean_inc(v_buildTime_6763_);
lean_inc(v_trace_6762_);
lean_inc(v_log_6759_);
lean_dec(v___y_6757_);
v___x_6765_ = lean_box(0);
v_isShared_6766_ = v_isSharedCheck_6820_;
goto v_resetjp_6764_;
}
v_resetjp_6764_:
{
lean_object* v_leanTrace_6767_; lean_object* v___f_6768_; lean_object* v___x_6769_; uint64_t v___y_6771_; uint64_t v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; uint8_t v___x_6812_; 
v_leanTrace_6767_ = lean_ctor_get(v___y_6756_, 2);
lean_inc_ref(v_oFile_6749_);
lean_inc_ref(v_traceArgs_6748_);
v___f_6768_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6768_, 0, v_weakArgs_6747_);
lean_closure_set(v___f_6768_, 1, v_traceArgs_6748_);
lean_closure_set(v___f_6768_, 2, v_oFile_6749_);
lean_closure_set(v___f_6768_, 3, v_srcFile_6751_);
lean_closure_set(v___f_6768_, 4, v_leanIncludeDir_x3f_6750_);
lean_inc_ref(v_leanTrace_6767_);
v___x_6769_ = l_Lake_BuildTrace_mix(v_trace_6762_, v_leanTrace_6767_);
v___x_6809_ = l_Lake_Hash_nil;
v___x_6810_ = lean_unsigned_to_nat(0u);
v___x_6811_ = lean_array_get_size(v_traceArgs_6748_);
v___x_6812_ = lean_nat_dec_lt(v___x_6810_, v___x_6811_);
if (v___x_6812_ == 0)
{
v___y_6771_ = v___x_6809_;
goto v___jp_6770_;
}
else
{
uint8_t v___x_6813_; 
v___x_6813_ = lean_nat_dec_le(v___x_6811_, v___x_6811_);
if (v___x_6813_ == 0)
{
if (v___x_6812_ == 0)
{
v___y_6771_ = v___x_6809_;
goto v___jp_6770_;
}
else
{
size_t v___x_6814_; size_t v___x_6815_; uint64_t v___x_6816_; 
v___x_6814_ = ((size_t)0ULL);
v___x_6815_ = lean_usize_of_nat(v___x_6811_);
v___x_6816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6748_, v___x_6814_, v___x_6815_, v___x_6809_);
v___y_6771_ = v___x_6816_;
goto v___jp_6770_;
}
}
else
{
size_t v___x_6817_; size_t v___x_6818_; uint64_t v___x_6819_; 
v___x_6817_ = ((size_t)0ULL);
v___x_6818_ = lean_usize_of_nat(v___x_6811_);
v___x_6819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6748_, v___x_6817_, v___x_6818_, v___x_6809_);
v___y_6771_ = v___x_6819_;
goto v___jp_6770_;
}
}
v___jp_6770_:
{
lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6785_; 
v___x_6772_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6773_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6774_ = lean_array_to_list(v_traceArgs_6748_);
v___x_6775_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6774_);
lean_dec(v___x_6774_);
v___x_6776_ = lean_string_append(v___x_6773_, v___x_6775_);
lean_dec_ref(v___x_6775_);
v___x_6777_ = lean_string_append(v___x_6772_, v___x_6776_);
lean_dec_ref(v___x_6776_);
v___x_6778_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6779_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6780_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6780_, 0, v___x_6777_);
lean_ctor_set(v___x_6780_, 1, v___x_6778_);
lean_ctor_set(v___x_6780_, 2, v___x_6779_);
lean_ctor_set_uint64(v___x_6780_, sizeof(void*)*3, v___y_6771_);
v___x_6781_ = l_Lake_BuildTrace_mix(v___x_6769_, v___x_6780_);
v___x_6782_ = l_Lake_platformTrace;
v___x_6783_ = l_Lake_BuildTrace_mix(v___x_6781_, v___x_6782_);
if (v_isShared_6766_ == 0)
{
lean_ctor_set(v___x_6765_, 1, v___x_6783_);
v___x_6785_ = v___x_6765_;
goto v_reusejp_6784_;
}
else
{
lean_object* v_reuseFailAlloc_6808_; 
v_reuseFailAlloc_6808_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6808_, 0, v_log_6759_);
lean_ctor_set(v_reuseFailAlloc_6808_, 1, v___x_6783_);
lean_ctor_set(v_reuseFailAlloc_6808_, 2, v_buildTime_6763_);
lean_ctor_set_uint8(v_reuseFailAlloc_6808_, sizeof(void*)*3, v_action_6760_);
lean_ctor_set_uint8(v_reuseFailAlloc_6808_, sizeof(void*)*3 + 1, v_wantsRebuild_6761_);
v___x_6785_ = v_reuseFailAlloc_6808_;
goto v_reusejp_6784_;
}
v_reusejp_6784_:
{
uint8_t v___x_6786_; lean_object* v___x_6787_; lean_object* v___x_6788_; 
v___x_6786_ = 0;
v___x_6787_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6788_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6749_, v___f_6768_, v___x_6786_, v___x_6787_, v___x_6786_, v___x_6786_, v___x_6786_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___x_6785_);
if (lean_obj_tag(v___x_6788_) == 0)
{
lean_object* v_a_6789_; lean_object* v_a_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6798_; 
v_a_6789_ = lean_ctor_get(v___x_6788_, 0);
v_a_6790_ = lean_ctor_get(v___x_6788_, 1);
v_isSharedCheck_6798_ = !lean_is_exclusive(v___x_6788_);
if (v_isSharedCheck_6798_ == 0)
{
v___x_6792_ = v___x_6788_;
v_isShared_6793_ = v_isSharedCheck_6798_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_a_6790_);
lean_inc(v_a_6789_);
lean_dec(v___x_6788_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6798_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v_path_6794_; lean_object* v___x_6796_; 
v_path_6794_ = lean_ctor_get(v_a_6789_, 1);
lean_inc_ref(v_path_6794_);
lean_dec(v_a_6789_);
if (v_isShared_6793_ == 0)
{
lean_ctor_set(v___x_6792_, 0, v_path_6794_);
v___x_6796_ = v___x_6792_;
goto v_reusejp_6795_;
}
else
{
lean_object* v_reuseFailAlloc_6797_; 
v_reuseFailAlloc_6797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6797_, 0, v_path_6794_);
lean_ctor_set(v_reuseFailAlloc_6797_, 1, v_a_6790_);
v___x_6796_ = v_reuseFailAlloc_6797_;
goto v_reusejp_6795_;
}
v_reusejp_6795_:
{
return v___x_6796_;
}
}
}
else
{
lean_object* v_a_6799_; lean_object* v_a_6800_; lean_object* v___x_6802_; uint8_t v_isShared_6803_; uint8_t v_isSharedCheck_6807_; 
v_a_6799_ = lean_ctor_get(v___x_6788_, 0);
v_a_6800_ = lean_ctor_get(v___x_6788_, 1);
v_isSharedCheck_6807_ = !lean_is_exclusive(v___x_6788_);
if (v_isSharedCheck_6807_ == 0)
{
v___x_6802_ = v___x_6788_;
v_isShared_6803_ = v_isSharedCheck_6807_;
goto v_resetjp_6801_;
}
else
{
lean_inc(v_a_6800_);
lean_inc(v_a_6799_);
lean_dec(v___x_6788_);
v___x_6802_ = lean_box(0);
v_isShared_6803_ = v_isSharedCheck_6807_;
goto v_resetjp_6801_;
}
v_resetjp_6801_:
{
lean_object* v___x_6805_; 
if (v_isShared_6803_ == 0)
{
v___x_6805_ = v___x_6802_;
goto v_reusejp_6804_;
}
else
{
lean_object* v_reuseFailAlloc_6806_; 
v_reuseFailAlloc_6806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6806_, 0, v_a_6799_);
lean_ctor_set(v_reuseFailAlloc_6806_, 1, v_a_6800_);
v___x_6805_ = v_reuseFailAlloc_6806_;
goto v_reusejp_6804_;
}
v_reusejp_6804_:
{
return v___x_6805_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6821_, lean_object* v_traceArgs_6822_, lean_object* v_oFile_6823_, lean_object* v_leanIncludeDir_x3f_6824_, lean_object* v_srcFile_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_){
_start:
{
lean_object* v_res_6833_; 
v_res_6833_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6821_, v_traceArgs_6822_, v_oFile_6823_, v_leanIncludeDir_x3f_6824_, v_srcFile_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_);
lean_dec_ref(v___y_6830_);
lean_dec(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec(v___y_6827_);
return v_res_6833_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6834_, lean_object* v_srcJob_6835_, lean_object* v_weakArgs_6836_, lean_object* v_traceArgs_6837_, lean_object* v_leanIncludeDir_x3f_6838_, lean_object* v_a_6839_, lean_object* v_a_6840_, lean_object* v_a_6841_, lean_object* v_a_6842_, lean_object* v_a_6843_, lean_object* v_a_6844_){
_start:
{
lean_object* v___f_6846_; lean_object* v___x_6847_; lean_object* v___x_6848_; uint8_t v___x_6849_; lean_object* v___x_6850_; 
v___f_6846_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6846_, 0, v_weakArgs_6836_);
lean_closure_set(v___f_6846_, 1, v_traceArgs_6837_);
lean_closure_set(v___f_6846_, 2, v_oFile_6834_);
lean_closure_set(v___f_6846_, 3, v_leanIncludeDir_x3f_6838_);
v___x_6847_ = l_Lake_instDataKindFilePath;
v___x_6848_ = lean_unsigned_to_nat(0u);
v___x_6849_ = 0;
v___x_6850_ = l_Lake_Job_mapM___redArg(v___x_6847_, v_srcJob_6835_, v___f_6846_, v___x_6848_, v___x_6849_, v_a_6839_, v_a_6840_, v_a_6841_, v_a_6842_, v_a_6843_, v_a_6844_);
return v___x_6850_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6851_, lean_object* v_srcJob_6852_, lean_object* v_weakArgs_6853_, lean_object* v_traceArgs_6854_, lean_object* v_leanIncludeDir_x3f_6855_, lean_object* v_a_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_, lean_object* v_a_6859_, lean_object* v_a_6860_, lean_object* v_a_6861_, lean_object* v_a_6862_){
_start:
{
lean_object* v_res_6863_; 
v_res_6863_ = l_Lake_buildLeanO(v_oFile_6851_, v_srcJob_6852_, v_weakArgs_6853_, v_traceArgs_6854_, v_leanIncludeDir_x3f_6855_, v_a_6856_, v_a_6857_, v_a_6858_, v_a_6859_, v_a_6860_, v_a_6861_);
lean_dec_ref(v_a_6861_);
lean_dec_ref(v_a_6860_);
lean_dec(v_a_6859_);
lean_dec(v_a_6858_);
lean_dec(v_a_6857_);
return v_res_6863_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6864_, lean_object* v_oFiles_6865_, uint8_t v_thin_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_, lean_object* v___y_6870_, lean_object* v___y_6871_, lean_object* v___y_6872_){
_start:
{
lean_object* v_toContext_6874_; lean_object* v_lakeEnv_6875_; lean_object* v_lean_6876_; lean_object* v_log_6877_; uint8_t v_action_6878_; uint8_t v_wantsRebuild_6879_; lean_object* v_trace_6880_; lean_object* v_buildTime_6881_; lean_object* v___x_6883_; uint8_t v_isShared_6884_; uint8_t v_isSharedCheck_6911_; 
v_toContext_6874_ = lean_ctor_get(v___y_6871_, 1);
v_lakeEnv_6875_ = lean_ctor_get(v_toContext_6874_, 0);
v_lean_6876_ = lean_ctor_get(v_lakeEnv_6875_, 1);
v_log_6877_ = lean_ctor_get(v___y_6872_, 0);
v_action_6878_ = lean_ctor_get_uint8(v___y_6872_, sizeof(void*)*3);
v_wantsRebuild_6879_ = lean_ctor_get_uint8(v___y_6872_, sizeof(void*)*3 + 1);
v_trace_6880_ = lean_ctor_get(v___y_6872_, 1);
v_buildTime_6881_ = lean_ctor_get(v___y_6872_, 2);
v_isSharedCheck_6911_ = !lean_is_exclusive(v___y_6872_);
if (v_isSharedCheck_6911_ == 0)
{
v___x_6883_ = v___y_6872_;
v_isShared_6884_ = v_isSharedCheck_6911_;
goto v_resetjp_6882_;
}
else
{
lean_inc(v_buildTime_6881_);
lean_inc(v_trace_6880_);
lean_inc(v_log_6877_);
lean_dec(v___y_6872_);
v___x_6883_ = lean_box(0);
v_isShared_6884_ = v_isSharedCheck_6911_;
goto v_resetjp_6882_;
}
v_resetjp_6882_:
{
lean_object* v_ar_6885_; lean_object* v___x_6886_; 
v_ar_6885_ = lean_ctor_get(v_lean_6876_, 13);
lean_inc_ref(v_ar_6885_);
v___x_6886_ = l_Lake_compileStaticLib(v_libFile_6864_, v_oFiles_6865_, v_ar_6885_, v_thin_6866_, v_log_6877_);
if (lean_obj_tag(v___x_6886_) == 0)
{
lean_object* v_a_6887_; lean_object* v_a_6888_; lean_object* v___x_6890_; uint8_t v_isShared_6891_; uint8_t v_isSharedCheck_6898_; 
v_a_6887_ = lean_ctor_get(v___x_6886_, 0);
v_a_6888_ = lean_ctor_get(v___x_6886_, 1);
v_isSharedCheck_6898_ = !lean_is_exclusive(v___x_6886_);
if (v_isSharedCheck_6898_ == 0)
{
v___x_6890_ = v___x_6886_;
v_isShared_6891_ = v_isSharedCheck_6898_;
goto v_resetjp_6889_;
}
else
{
lean_inc(v_a_6888_);
lean_inc(v_a_6887_);
lean_dec(v___x_6886_);
v___x_6890_ = lean_box(0);
v_isShared_6891_ = v_isSharedCheck_6898_;
goto v_resetjp_6889_;
}
v_resetjp_6889_:
{
lean_object* v___x_6893_; 
if (v_isShared_6884_ == 0)
{
lean_ctor_set(v___x_6883_, 0, v_a_6888_);
v___x_6893_ = v___x_6883_;
goto v_reusejp_6892_;
}
else
{
lean_object* v_reuseFailAlloc_6897_; 
v_reuseFailAlloc_6897_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6897_, 0, v_a_6888_);
lean_ctor_set(v_reuseFailAlloc_6897_, 1, v_trace_6880_);
lean_ctor_set(v_reuseFailAlloc_6897_, 2, v_buildTime_6881_);
lean_ctor_set_uint8(v_reuseFailAlloc_6897_, sizeof(void*)*3, v_action_6878_);
lean_ctor_set_uint8(v_reuseFailAlloc_6897_, sizeof(void*)*3 + 1, v_wantsRebuild_6879_);
v___x_6893_ = v_reuseFailAlloc_6897_;
goto v_reusejp_6892_;
}
v_reusejp_6892_:
{
lean_object* v___x_6895_; 
if (v_isShared_6891_ == 0)
{
lean_ctor_set(v___x_6890_, 1, v___x_6893_);
v___x_6895_ = v___x_6890_;
goto v_reusejp_6894_;
}
else
{
lean_object* v_reuseFailAlloc_6896_; 
v_reuseFailAlloc_6896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6887_);
lean_ctor_set(v_reuseFailAlloc_6896_, 1, v___x_6893_);
v___x_6895_ = v_reuseFailAlloc_6896_;
goto v_reusejp_6894_;
}
v_reusejp_6894_:
{
return v___x_6895_;
}
}
}
}
else
{
lean_object* v_a_6899_; lean_object* v_a_6900_; lean_object* v___x_6902_; uint8_t v_isShared_6903_; uint8_t v_isSharedCheck_6910_; 
v_a_6899_ = lean_ctor_get(v___x_6886_, 0);
v_a_6900_ = lean_ctor_get(v___x_6886_, 1);
v_isSharedCheck_6910_ = !lean_is_exclusive(v___x_6886_);
if (v_isSharedCheck_6910_ == 0)
{
v___x_6902_ = v___x_6886_;
v_isShared_6903_ = v_isSharedCheck_6910_;
goto v_resetjp_6901_;
}
else
{
lean_inc(v_a_6900_);
lean_inc(v_a_6899_);
lean_dec(v___x_6886_);
v___x_6902_ = lean_box(0);
v_isShared_6903_ = v_isSharedCheck_6910_;
goto v_resetjp_6901_;
}
v_resetjp_6901_:
{
lean_object* v___x_6905_; 
if (v_isShared_6884_ == 0)
{
lean_ctor_set(v___x_6883_, 0, v_a_6900_);
v___x_6905_ = v___x_6883_;
goto v_reusejp_6904_;
}
else
{
lean_object* v_reuseFailAlloc_6909_; 
v_reuseFailAlloc_6909_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6909_, 0, v_a_6900_);
lean_ctor_set(v_reuseFailAlloc_6909_, 1, v_trace_6880_);
lean_ctor_set(v_reuseFailAlloc_6909_, 2, v_buildTime_6881_);
lean_ctor_set_uint8(v_reuseFailAlloc_6909_, sizeof(void*)*3, v_action_6878_);
lean_ctor_set_uint8(v_reuseFailAlloc_6909_, sizeof(void*)*3 + 1, v_wantsRebuild_6879_);
v___x_6905_ = v_reuseFailAlloc_6909_;
goto v_reusejp_6904_;
}
v_reusejp_6904_:
{
lean_object* v___x_6907_; 
if (v_isShared_6903_ == 0)
{
lean_ctor_set(v___x_6902_, 1, v___x_6905_);
v___x_6907_ = v___x_6902_;
goto v_reusejp_6906_;
}
else
{
lean_object* v_reuseFailAlloc_6908_; 
v_reuseFailAlloc_6908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6899_);
lean_ctor_set(v_reuseFailAlloc_6908_, 1, v___x_6905_);
v___x_6907_ = v_reuseFailAlloc_6908_;
goto v_reusejp_6906_;
}
v_reusejp_6906_:
{
return v___x_6907_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6912_, lean_object* v_oFiles_6913_, lean_object* v_thin_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_){
_start:
{
uint8_t v_thin_boxed_6922_; lean_object* v_res_6923_; 
v_thin_boxed_6922_ = lean_unbox(v_thin_6914_);
v_res_6923_ = l_Lake_buildStaticLib___lam__0(v_libFile_6912_, v_oFiles_6913_, v_thin_boxed_6922_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_);
lean_dec_ref(v___y_6919_);
lean_dec(v___y_6918_);
lean_dec(v___y_6917_);
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
return v_res_6923_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6925_, uint8_t v_thin_6926_, lean_object* v_oFiles_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_){
_start:
{
lean_object* v___x_6935_; lean_object* v___f_6936_; uint8_t v___x_6937_; lean_object* v___x_6938_; uint8_t v___x_6939_; lean_object* v___x_6940_; 
v___x_6935_ = lean_box(v_thin_6926_);
lean_inc_ref(v_libFile_6925_);
v___f_6936_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6936_, 0, v_libFile_6925_);
lean_closure_set(v___f_6936_, 1, v_oFiles_6927_);
lean_closure_set(v___f_6936_, 2, v___x_6935_);
v___x_6937_ = 0;
v___x_6938_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6939_ = 1;
v___x_6940_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6925_, v___f_6936_, v___x_6937_, v___x_6938_, v___x_6939_, v___x_6937_, v___x_6937_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_);
if (lean_obj_tag(v___x_6940_) == 0)
{
lean_object* v_a_6941_; lean_object* v_a_6942_; lean_object* v___x_6944_; uint8_t v_isShared_6945_; uint8_t v_isSharedCheck_6950_; 
v_a_6941_ = lean_ctor_get(v___x_6940_, 0);
v_a_6942_ = lean_ctor_get(v___x_6940_, 1);
v_isSharedCheck_6950_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6950_ == 0)
{
v___x_6944_ = v___x_6940_;
v_isShared_6945_ = v_isSharedCheck_6950_;
goto v_resetjp_6943_;
}
else
{
lean_inc(v_a_6942_);
lean_inc(v_a_6941_);
lean_dec(v___x_6940_);
v___x_6944_ = lean_box(0);
v_isShared_6945_ = v_isSharedCheck_6950_;
goto v_resetjp_6943_;
}
v_resetjp_6943_:
{
lean_object* v_path_6946_; lean_object* v___x_6948_; 
v_path_6946_ = lean_ctor_get(v_a_6941_, 1);
lean_inc_ref(v_path_6946_);
lean_dec(v_a_6941_);
if (v_isShared_6945_ == 0)
{
lean_ctor_set(v___x_6944_, 0, v_path_6946_);
v___x_6948_ = v___x_6944_;
goto v_reusejp_6947_;
}
else
{
lean_object* v_reuseFailAlloc_6949_; 
v_reuseFailAlloc_6949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6949_, 0, v_path_6946_);
lean_ctor_set(v_reuseFailAlloc_6949_, 1, v_a_6942_);
v___x_6948_ = v_reuseFailAlloc_6949_;
goto v_reusejp_6947_;
}
v_reusejp_6947_:
{
return v___x_6948_;
}
}
}
else
{
lean_object* v_a_6951_; lean_object* v_a_6952_; lean_object* v___x_6954_; uint8_t v_isShared_6955_; uint8_t v_isSharedCheck_6959_; 
v_a_6951_ = lean_ctor_get(v___x_6940_, 0);
v_a_6952_ = lean_ctor_get(v___x_6940_, 1);
v_isSharedCheck_6959_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6959_ == 0)
{
v___x_6954_ = v___x_6940_;
v_isShared_6955_ = v_isSharedCheck_6959_;
goto v_resetjp_6953_;
}
else
{
lean_inc(v_a_6952_);
lean_inc(v_a_6951_);
lean_dec(v___x_6940_);
v___x_6954_ = lean_box(0);
v_isShared_6955_ = v_isSharedCheck_6959_;
goto v_resetjp_6953_;
}
v_resetjp_6953_:
{
lean_object* v___x_6957_; 
if (v_isShared_6955_ == 0)
{
v___x_6957_ = v___x_6954_;
goto v_reusejp_6956_;
}
else
{
lean_object* v_reuseFailAlloc_6958_; 
v_reuseFailAlloc_6958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6951_);
lean_ctor_set(v_reuseFailAlloc_6958_, 1, v_a_6952_);
v___x_6957_ = v_reuseFailAlloc_6958_;
goto v_reusejp_6956_;
}
v_reusejp_6956_:
{
return v___x_6957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6960_, lean_object* v_thin_6961_, lean_object* v_oFiles_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_){
_start:
{
uint8_t v_thin_boxed_6970_; lean_object* v_res_6971_; 
v_thin_boxed_6970_ = lean_unbox(v_thin_6961_);
v_res_6971_ = l_Lake_buildStaticLib___lam__1(v_libFile_6960_, v_thin_boxed_6970_, v_oFiles_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_);
lean_dec_ref(v___y_6967_);
lean_dec(v___y_6966_);
lean_dec(v___y_6965_);
lean_dec(v___y_6964_);
return v_res_6971_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6973_, lean_object* v_oFileJobs_6974_, uint8_t v_thin_6975_, lean_object* v_a_6976_, lean_object* v_a_6977_, lean_object* v_a_6978_, lean_object* v_a_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_){
_start:
{
lean_object* v___x_6983_; lean_object* v___f_6984_; lean_object* v___x_6985_; lean_object* v___x_6986_; lean_object* v___x_6987_; lean_object* v___x_6988_; uint8_t v___x_6989_; lean_object* v___x_6990_; 
v___x_6983_ = lean_box(v_thin_6975_);
v___f_6984_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6984_, 0, v_libFile_6973_);
lean_closure_set(v___f_6984_, 1, v___x_6983_);
v___x_6985_ = l_Lake_instDataKindFilePath;
v___x_6986_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6987_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6974_, v___x_6986_);
v___x_6988_ = lean_unsigned_to_nat(0u);
v___x_6989_ = 0;
v___x_6990_ = l_Lake_Job_mapM___redArg(v___x_6985_, v___x_6987_, v___f_6984_, v___x_6988_, v___x_6989_, v_a_6976_, v_a_6977_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
return v___x_6990_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6991_, lean_object* v_oFileJobs_6992_, lean_object* v_thin_6993_, lean_object* v_a_6994_, lean_object* v_a_6995_, lean_object* v_a_6996_, lean_object* v_a_6997_, lean_object* v_a_6998_, lean_object* v_a_6999_, lean_object* v_a_7000_){
_start:
{
uint8_t v_thin_boxed_7001_; lean_object* v_res_7002_; 
v_thin_boxed_7001_ = lean_unbox(v_thin_6993_);
v_res_7002_ = l_Lake_buildStaticLib(v_libFile_6991_, v_oFileJobs_6992_, v_thin_boxed_7001_, v_a_6994_, v_a_6995_, v_a_6996_, v_a_6997_, v_a_6998_, v_a_6999_);
lean_dec_ref(v_a_6999_);
lean_dec_ref(v_a_6998_);
lean_dec(v_a_6997_);
lean_dec(v_a_6996_);
lean_dec(v_a_6995_);
lean_dec_ref(v_oFileJobs_6992_);
return v_res_7002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7003_, size_t v_sz_7004_, size_t v_i_7005_, lean_object* v_b_7006_){
_start:
{
uint8_t v___x_7007_; 
v___x_7007_ = lean_usize_dec_lt(v_i_7005_, v_sz_7004_);
if (v___x_7007_ == 0)
{
return v_b_7006_;
}
else
{
lean_object* v_a_7008_; lean_object* v___x_7009_; size_t v___x_7010_; size_t v___x_7011_; 
v_a_7008_ = lean_array_uget_borrowed(v_as_7003_, v_i_7005_);
lean_inc(v_a_7008_);
v___x_7009_ = lean_array_push(v_b_7006_, v_a_7008_);
v___x_7010_ = ((size_t)1ULL);
v___x_7011_ = lean_usize_add(v_i_7005_, v___x_7010_);
v_i_7005_ = v___x_7011_;
v_b_7006_ = v___x_7009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7013_, lean_object* v_sz_7014_, lean_object* v_i_7015_, lean_object* v_b_7016_){
_start:
{
size_t v_sz_boxed_7017_; size_t v_i_boxed_7018_; lean_object* v_res_7019_; 
v_sz_boxed_7017_ = lean_unbox_usize(v_sz_7014_);
lean_dec(v_sz_7014_);
v_i_boxed_7018_ = lean_unbox_usize(v_i_7015_);
lean_dec(v_i_7015_);
v_res_7019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7013_, v_sz_boxed_7017_, v_i_boxed_7018_, v_b_7016_);
lean_dec_ref(v_as_7013_);
return v_res_7019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7022_, size_t v_sz_7023_, size_t v_i_7024_, lean_object* v_b_7025_){
_start:
{
uint8_t v___x_7026_; 
v___x_7026_ = lean_usize_dec_lt(v_i_7024_, v_sz_7023_);
if (v___x_7026_ == 0)
{
return v_b_7025_;
}
else
{
lean_object* v_a_7027_; lean_object* v_args_7029_; lean_object* v___x_7037_; 
v_a_7027_ = lean_array_uget_borrowed(v_as_7022_, v_i_7024_);
lean_inc(v_a_7027_);
v___x_7037_ = l_Lake_Dynlib_dir_x3f(v_a_7027_);
if (lean_obj_tag(v___x_7037_) == 1)
{
lean_object* v_val_7038_; lean_object* v___x_7039_; lean_object* v___x_7040_; lean_object* v___x_7041_; 
v_val_7038_ = lean_ctor_get(v___x_7037_, 0);
lean_inc(v_val_7038_);
lean_dec_ref_known(v___x_7037_, 1);
v___x_7039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7040_ = lean_string_append(v___x_7039_, v_val_7038_);
lean_dec(v_val_7038_);
v___x_7041_ = lean_array_push(v_b_7025_, v___x_7040_);
v_args_7029_ = v___x_7041_;
goto v___jp_7028_;
}
else
{
lean_dec(v___x_7037_);
v_args_7029_ = v_b_7025_;
goto v___jp_7028_;
}
v___jp_7028_:
{
lean_object* v_name_7030_; lean_object* v___x_7031_; lean_object* v___x_7032_; lean_object* v___x_7033_; size_t v___x_7034_; size_t v___x_7035_; 
v_name_7030_ = lean_ctor_get(v_a_7027_, 1);
v___x_7031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7032_ = lean_string_append(v___x_7031_, v_name_7030_);
v___x_7033_ = lean_array_push(v_args_7029_, v___x_7032_);
v___x_7034_ = ((size_t)1ULL);
v___x_7035_ = lean_usize_add(v_i_7024_, v___x_7034_);
v_i_7024_ = v___x_7035_;
v_b_7025_ = v___x_7033_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7042_, lean_object* v_sz_7043_, lean_object* v_i_7044_, lean_object* v_b_7045_){
_start:
{
size_t v_sz_boxed_7046_; size_t v_i_boxed_7047_; lean_object* v_res_7048_; 
v_sz_boxed_7046_ = lean_unbox_usize(v_sz_7043_);
lean_dec(v_sz_7043_);
v_i_boxed_7047_ = lean_unbox_usize(v_i_7044_);
lean_dec(v_i_7044_);
v_res_7048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7042_, v_sz_boxed_7046_, v_i_boxed_7047_, v_b_7045_);
lean_dec_ref(v_as_7042_);
return v_res_7048_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7049_, lean_object* v_libs_7050_){
_start:
{
lean_object* v_args_7051_; size_t v_sz_7052_; size_t v___x_7053_; lean_object* v___x_7054_; size_t v_sz_7055_; lean_object* v___x_7056_; 
v_args_7051_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7052_ = lean_array_size(v_objs_7049_);
v___x_7053_ = ((size_t)0ULL);
v___x_7054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7049_, v_sz_7052_, v___x_7053_, v_args_7051_);
v_sz_7055_ = lean_array_size(v_libs_7050_);
v___x_7056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7050_, v_sz_7055_, v___x_7053_, v___x_7054_);
return v___x_7056_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7057_, lean_object* v_libs_7058_){
_start:
{
lean_object* v_res_7059_; 
v_res_7059_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7057_, v_libs_7058_);
lean_dec_ref(v_libs_7058_);
lean_dec_ref(v_objs_7057_);
return v_res_7059_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7060_, lean_object* v_t_7061_){
_start:
{
if (lean_obj_tag(v_t_7061_) == 0)
{
lean_object* v_k_7062_; lean_object* v_l_7063_; lean_object* v_r_7064_; uint8_t v___x_7065_; 
v_k_7062_ = lean_ctor_get(v_t_7061_, 1);
v_l_7063_ = lean_ctor_get(v_t_7061_, 3);
v_r_7064_ = lean_ctor_get(v_t_7061_, 4);
v___x_7065_ = lean_string_compare(v_k_7060_, v_k_7062_);
switch(v___x_7065_)
{
case 0:
{
v_t_7061_ = v_l_7063_;
goto _start;
}
case 1:
{
uint8_t v___x_7067_; 
v___x_7067_ = 1;
return v___x_7067_;
}
default: 
{
v_t_7061_ = v_r_7064_;
goto _start;
}
}
}
else
{
uint8_t v___x_7069_; 
v___x_7069_ = 0;
return v___x_7069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7070_, lean_object* v_t_7071_){
_start:
{
uint8_t v_res_7072_; lean_object* v_r_7073_; 
v_res_7072_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7070_, v_t_7071_);
lean_dec(v_t_7071_);
lean_dec_ref(v_k_7070_);
v_r_7073_ = lean_box(v_res_7072_);
return v_r_7073_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7074_, lean_object* v_x_7075_){
_start:
{
if (lean_obj_tag(v_x_7075_) == 0)
{
uint8_t v___x_7076_; 
v___x_7076_ = 0;
return v___x_7076_;
}
else
{
lean_object* v_head_7077_; lean_object* v_tail_7078_; uint8_t v___x_7079_; 
v_head_7077_ = lean_ctor_get(v_x_7075_, 0);
v_tail_7078_ = lean_ctor_get(v_x_7075_, 1);
v___x_7079_ = lean_string_dec_eq(v_a_7074_, v_head_7077_);
if (v___x_7079_ == 0)
{
v_x_7075_ = v_tail_7078_;
goto _start;
}
else
{
return v___x_7079_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7081_, lean_object* v_x_7082_){
_start:
{
uint8_t v_res_7083_; lean_object* v_r_7084_; 
v_res_7083_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7081_, v_x_7082_);
lean_dec(v_x_7082_);
lean_dec_ref(v_a_7081_);
v_r_7084_ = lean_box(v_res_7083_);
return v_r_7084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7085_, lean_object* v_v_7086_, lean_object* v_t_7087_){
_start:
{
if (lean_obj_tag(v_t_7087_) == 0)
{
lean_object* v_size_7088_; lean_object* v_k_7089_; lean_object* v_v_7090_; lean_object* v_l_7091_; lean_object* v_r_7092_; lean_object* v___x_7094_; uint8_t v_isShared_7095_; uint8_t v_isSharedCheck_7372_; 
v_size_7088_ = lean_ctor_get(v_t_7087_, 0);
v_k_7089_ = lean_ctor_get(v_t_7087_, 1);
v_v_7090_ = lean_ctor_get(v_t_7087_, 2);
v_l_7091_ = lean_ctor_get(v_t_7087_, 3);
v_r_7092_ = lean_ctor_get(v_t_7087_, 4);
v_isSharedCheck_7372_ = !lean_is_exclusive(v_t_7087_);
if (v_isSharedCheck_7372_ == 0)
{
v___x_7094_ = v_t_7087_;
v_isShared_7095_ = v_isSharedCheck_7372_;
goto v_resetjp_7093_;
}
else
{
lean_inc(v_r_7092_);
lean_inc(v_l_7091_);
lean_inc(v_v_7090_);
lean_inc(v_k_7089_);
lean_inc(v_size_7088_);
lean_dec(v_t_7087_);
v___x_7094_ = lean_box(0);
v_isShared_7095_ = v_isSharedCheck_7372_;
goto v_resetjp_7093_;
}
v_resetjp_7093_:
{
uint8_t v___x_7096_; 
v___x_7096_ = lean_string_compare(v_k_7085_, v_k_7089_);
switch(v___x_7096_)
{
case 0:
{
lean_object* v_impl_7097_; lean_object* v___x_7098_; 
lean_dec(v_size_7088_);
v_impl_7097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7085_, v_v_7086_, v_l_7091_);
v___x_7098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7092_) == 0)
{
lean_object* v_size_7099_; lean_object* v_size_7100_; lean_object* v_k_7101_; lean_object* v_v_7102_; lean_object* v_l_7103_; lean_object* v_r_7104_; lean_object* v___x_7105_; lean_object* v___x_7106_; uint8_t v___x_7107_; 
v_size_7099_ = lean_ctor_get(v_r_7092_, 0);
v_size_7100_ = lean_ctor_get(v_impl_7097_, 0);
lean_inc(v_size_7100_);
v_k_7101_ = lean_ctor_get(v_impl_7097_, 1);
lean_inc(v_k_7101_);
v_v_7102_ = lean_ctor_get(v_impl_7097_, 2);
lean_inc(v_v_7102_);
v_l_7103_ = lean_ctor_get(v_impl_7097_, 3);
lean_inc(v_l_7103_);
v_r_7104_ = lean_ctor_get(v_impl_7097_, 4);
lean_inc(v_r_7104_);
v___x_7105_ = lean_unsigned_to_nat(3u);
v___x_7106_ = lean_nat_mul(v___x_7105_, v_size_7099_);
v___x_7107_ = lean_nat_dec_lt(v___x_7106_, v_size_7100_);
lean_dec(v___x_7106_);
if (v___x_7107_ == 0)
{
lean_object* v___x_7108_; lean_object* v___x_7109_; lean_object* v___x_7111_; 
lean_dec(v_r_7104_);
lean_dec(v_l_7103_);
lean_dec(v_v_7102_);
lean_dec(v_k_7101_);
v___x_7108_ = lean_nat_add(v___x_7098_, v_size_7100_);
lean_dec(v_size_7100_);
v___x_7109_ = lean_nat_add(v___x_7108_, v_size_7099_);
lean_dec(v___x_7108_);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 3, v_impl_7097_);
lean_ctor_set(v___x_7094_, 0, v___x_7109_);
v___x_7111_ = v___x_7094_;
goto v_reusejp_7110_;
}
else
{
lean_object* v_reuseFailAlloc_7112_; 
v_reuseFailAlloc_7112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7112_, 0, v___x_7109_);
lean_ctor_set(v_reuseFailAlloc_7112_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7112_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7112_, 3, v_impl_7097_);
lean_ctor_set(v_reuseFailAlloc_7112_, 4, v_r_7092_);
v___x_7111_ = v_reuseFailAlloc_7112_;
goto v_reusejp_7110_;
}
v_reusejp_7110_:
{
return v___x_7111_;
}
}
else
{
lean_object* v___x_7114_; uint8_t v_isShared_7115_; uint8_t v_isSharedCheck_7178_; 
v_isSharedCheck_7178_ = !lean_is_exclusive(v_impl_7097_);
if (v_isSharedCheck_7178_ == 0)
{
lean_object* v_unused_7179_; lean_object* v_unused_7180_; lean_object* v_unused_7181_; lean_object* v_unused_7182_; lean_object* v_unused_7183_; 
v_unused_7179_ = lean_ctor_get(v_impl_7097_, 4);
lean_dec(v_unused_7179_);
v_unused_7180_ = lean_ctor_get(v_impl_7097_, 3);
lean_dec(v_unused_7180_);
v_unused_7181_ = lean_ctor_get(v_impl_7097_, 2);
lean_dec(v_unused_7181_);
v_unused_7182_ = lean_ctor_get(v_impl_7097_, 1);
lean_dec(v_unused_7182_);
v_unused_7183_ = lean_ctor_get(v_impl_7097_, 0);
lean_dec(v_unused_7183_);
v___x_7114_ = v_impl_7097_;
v_isShared_7115_ = v_isSharedCheck_7178_;
goto v_resetjp_7113_;
}
else
{
lean_dec(v_impl_7097_);
v___x_7114_ = lean_box(0);
v_isShared_7115_ = v_isSharedCheck_7178_;
goto v_resetjp_7113_;
}
v_resetjp_7113_:
{
lean_object* v_size_7116_; lean_object* v_size_7117_; lean_object* v_k_7118_; lean_object* v_v_7119_; lean_object* v_l_7120_; lean_object* v_r_7121_; lean_object* v___x_7122_; lean_object* v___x_7123_; uint8_t v___x_7124_; 
v_size_7116_ = lean_ctor_get(v_l_7103_, 0);
v_size_7117_ = lean_ctor_get(v_r_7104_, 0);
v_k_7118_ = lean_ctor_get(v_r_7104_, 1);
v_v_7119_ = lean_ctor_get(v_r_7104_, 2);
v_l_7120_ = lean_ctor_get(v_r_7104_, 3);
v_r_7121_ = lean_ctor_get(v_r_7104_, 4);
v___x_7122_ = lean_unsigned_to_nat(2u);
v___x_7123_ = lean_nat_mul(v___x_7122_, v_size_7116_);
v___x_7124_ = lean_nat_dec_lt(v_size_7117_, v___x_7123_);
lean_dec(v___x_7123_);
if (v___x_7124_ == 0)
{
lean_object* v___x_7126_; uint8_t v_isShared_7127_; uint8_t v_isSharedCheck_7153_; 
lean_inc(v_r_7121_);
lean_inc(v_l_7120_);
lean_inc(v_v_7119_);
lean_inc(v_k_7118_);
v_isSharedCheck_7153_ = !lean_is_exclusive(v_r_7104_);
if (v_isSharedCheck_7153_ == 0)
{
lean_object* v_unused_7154_; lean_object* v_unused_7155_; lean_object* v_unused_7156_; lean_object* v_unused_7157_; lean_object* v_unused_7158_; 
v_unused_7154_ = lean_ctor_get(v_r_7104_, 4);
lean_dec(v_unused_7154_);
v_unused_7155_ = lean_ctor_get(v_r_7104_, 3);
lean_dec(v_unused_7155_);
v_unused_7156_ = lean_ctor_get(v_r_7104_, 2);
lean_dec(v_unused_7156_);
v_unused_7157_ = lean_ctor_get(v_r_7104_, 1);
lean_dec(v_unused_7157_);
v_unused_7158_ = lean_ctor_get(v_r_7104_, 0);
lean_dec(v_unused_7158_);
v___x_7126_ = v_r_7104_;
v_isShared_7127_ = v_isSharedCheck_7153_;
goto v_resetjp_7125_;
}
else
{
lean_dec(v_r_7104_);
v___x_7126_ = lean_box(0);
v_isShared_7127_ = v_isSharedCheck_7153_;
goto v_resetjp_7125_;
}
v_resetjp_7125_:
{
lean_object* v___x_7128_; lean_object* v___x_7129_; lean_object* v___y_7131_; lean_object* v___y_7132_; lean_object* v___y_7133_; lean_object* v___x_7141_; lean_object* v___y_7143_; 
v___x_7128_ = lean_nat_add(v___x_7098_, v_size_7100_);
lean_dec(v_size_7100_);
v___x_7129_ = lean_nat_add(v___x_7128_, v_size_7099_);
lean_dec(v___x_7128_);
v___x_7141_ = lean_nat_add(v___x_7098_, v_size_7116_);
if (lean_obj_tag(v_l_7120_) == 0)
{
lean_object* v_size_7151_; 
v_size_7151_ = lean_ctor_get(v_l_7120_, 0);
lean_inc(v_size_7151_);
v___y_7143_ = v_size_7151_;
goto v___jp_7142_;
}
else
{
lean_object* v___x_7152_; 
v___x_7152_ = lean_unsigned_to_nat(0u);
v___y_7143_ = v___x_7152_;
goto v___jp_7142_;
}
v___jp_7130_:
{
lean_object* v___x_7134_; lean_object* v___x_7136_; 
v___x_7134_ = lean_nat_add(v___y_7131_, v___y_7133_);
lean_dec(v___y_7133_);
lean_dec(v___y_7131_);
if (v_isShared_7127_ == 0)
{
lean_ctor_set(v___x_7126_, 4, v_r_7092_);
lean_ctor_set(v___x_7126_, 3, v_r_7121_);
lean_ctor_set(v___x_7126_, 2, v_v_7090_);
lean_ctor_set(v___x_7126_, 1, v_k_7089_);
lean_ctor_set(v___x_7126_, 0, v___x_7134_);
v___x_7136_ = v___x_7126_;
goto v_reusejp_7135_;
}
else
{
lean_object* v_reuseFailAlloc_7140_; 
v_reuseFailAlloc_7140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7140_, 0, v___x_7134_);
lean_ctor_set(v_reuseFailAlloc_7140_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7140_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7140_, 3, v_r_7121_);
lean_ctor_set(v_reuseFailAlloc_7140_, 4, v_r_7092_);
v___x_7136_ = v_reuseFailAlloc_7140_;
goto v_reusejp_7135_;
}
v_reusejp_7135_:
{
lean_object* v___x_7138_; 
if (v_isShared_7115_ == 0)
{
lean_ctor_set(v___x_7114_, 4, v___x_7136_);
lean_ctor_set(v___x_7114_, 3, v___y_7132_);
lean_ctor_set(v___x_7114_, 2, v_v_7119_);
lean_ctor_set(v___x_7114_, 1, v_k_7118_);
lean_ctor_set(v___x_7114_, 0, v___x_7129_);
v___x_7138_ = v___x_7114_;
goto v_reusejp_7137_;
}
else
{
lean_object* v_reuseFailAlloc_7139_; 
v_reuseFailAlloc_7139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7139_, 0, v___x_7129_);
lean_ctor_set(v_reuseFailAlloc_7139_, 1, v_k_7118_);
lean_ctor_set(v_reuseFailAlloc_7139_, 2, v_v_7119_);
lean_ctor_set(v_reuseFailAlloc_7139_, 3, v___y_7132_);
lean_ctor_set(v_reuseFailAlloc_7139_, 4, v___x_7136_);
v___x_7138_ = v_reuseFailAlloc_7139_;
goto v_reusejp_7137_;
}
v_reusejp_7137_:
{
return v___x_7138_;
}
}
}
v___jp_7142_:
{
lean_object* v___x_7144_; lean_object* v___x_7146_; 
v___x_7144_ = lean_nat_add(v___x_7141_, v___y_7143_);
lean_dec(v___y_7143_);
lean_dec(v___x_7141_);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_l_7120_);
lean_ctor_set(v___x_7094_, 3, v_l_7103_);
lean_ctor_set(v___x_7094_, 2, v_v_7102_);
lean_ctor_set(v___x_7094_, 1, v_k_7101_);
lean_ctor_set(v___x_7094_, 0, v___x_7144_);
v___x_7146_ = v___x_7094_;
goto v_reusejp_7145_;
}
else
{
lean_object* v_reuseFailAlloc_7150_; 
v_reuseFailAlloc_7150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7150_, 0, v___x_7144_);
lean_ctor_set(v_reuseFailAlloc_7150_, 1, v_k_7101_);
lean_ctor_set(v_reuseFailAlloc_7150_, 2, v_v_7102_);
lean_ctor_set(v_reuseFailAlloc_7150_, 3, v_l_7103_);
lean_ctor_set(v_reuseFailAlloc_7150_, 4, v_l_7120_);
v___x_7146_ = v_reuseFailAlloc_7150_;
goto v_reusejp_7145_;
}
v_reusejp_7145_:
{
lean_object* v___x_7147_; 
v___x_7147_ = lean_nat_add(v___x_7098_, v_size_7099_);
if (lean_obj_tag(v_r_7121_) == 0)
{
lean_object* v_size_7148_; 
v_size_7148_ = lean_ctor_get(v_r_7121_, 0);
lean_inc(v_size_7148_);
v___y_7131_ = v___x_7147_;
v___y_7132_ = v___x_7146_;
v___y_7133_ = v_size_7148_;
goto v___jp_7130_;
}
else
{
lean_object* v___x_7149_; 
v___x_7149_ = lean_unsigned_to_nat(0u);
v___y_7131_ = v___x_7147_;
v___y_7132_ = v___x_7146_;
v___y_7133_ = v___x_7149_;
goto v___jp_7130_;
}
}
}
}
}
else
{
lean_object* v___x_7159_; lean_object* v___x_7160_; lean_object* v___x_7161_; lean_object* v___x_7162_; lean_object* v___x_7164_; 
lean_del_object(v___x_7094_);
v___x_7159_ = lean_nat_add(v___x_7098_, v_size_7100_);
lean_dec(v_size_7100_);
v___x_7160_ = lean_nat_add(v___x_7159_, v_size_7099_);
lean_dec(v___x_7159_);
v___x_7161_ = lean_nat_add(v___x_7098_, v_size_7099_);
v___x_7162_ = lean_nat_add(v___x_7161_, v_size_7117_);
lean_dec(v___x_7161_);
lean_inc_ref(v_r_7092_);
if (v_isShared_7115_ == 0)
{
lean_ctor_set(v___x_7114_, 4, v_r_7092_);
lean_ctor_set(v___x_7114_, 3, v_r_7104_);
lean_ctor_set(v___x_7114_, 2, v_v_7090_);
lean_ctor_set(v___x_7114_, 1, v_k_7089_);
lean_ctor_set(v___x_7114_, 0, v___x_7162_);
v___x_7164_ = v___x_7114_;
goto v_reusejp_7163_;
}
else
{
lean_object* v_reuseFailAlloc_7177_; 
v_reuseFailAlloc_7177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7177_, 0, v___x_7162_);
lean_ctor_set(v_reuseFailAlloc_7177_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7177_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7177_, 3, v_r_7104_);
lean_ctor_set(v_reuseFailAlloc_7177_, 4, v_r_7092_);
v___x_7164_ = v_reuseFailAlloc_7177_;
goto v_reusejp_7163_;
}
v_reusejp_7163_:
{
lean_object* v___x_7166_; uint8_t v_isShared_7167_; uint8_t v_isSharedCheck_7171_; 
v_isSharedCheck_7171_ = !lean_is_exclusive(v_r_7092_);
if (v_isSharedCheck_7171_ == 0)
{
lean_object* v_unused_7172_; lean_object* v_unused_7173_; lean_object* v_unused_7174_; lean_object* v_unused_7175_; lean_object* v_unused_7176_; 
v_unused_7172_ = lean_ctor_get(v_r_7092_, 4);
lean_dec(v_unused_7172_);
v_unused_7173_ = lean_ctor_get(v_r_7092_, 3);
lean_dec(v_unused_7173_);
v_unused_7174_ = lean_ctor_get(v_r_7092_, 2);
lean_dec(v_unused_7174_);
v_unused_7175_ = lean_ctor_get(v_r_7092_, 1);
lean_dec(v_unused_7175_);
v_unused_7176_ = lean_ctor_get(v_r_7092_, 0);
lean_dec(v_unused_7176_);
v___x_7166_ = v_r_7092_;
v_isShared_7167_ = v_isSharedCheck_7171_;
goto v_resetjp_7165_;
}
else
{
lean_dec(v_r_7092_);
v___x_7166_ = lean_box(0);
v_isShared_7167_ = v_isSharedCheck_7171_;
goto v_resetjp_7165_;
}
v_resetjp_7165_:
{
lean_object* v___x_7169_; 
if (v_isShared_7167_ == 0)
{
lean_ctor_set(v___x_7166_, 4, v___x_7164_);
lean_ctor_set(v___x_7166_, 3, v_l_7103_);
lean_ctor_set(v___x_7166_, 2, v_v_7102_);
lean_ctor_set(v___x_7166_, 1, v_k_7101_);
lean_ctor_set(v___x_7166_, 0, v___x_7160_);
v___x_7169_ = v___x_7166_;
goto v_reusejp_7168_;
}
else
{
lean_object* v_reuseFailAlloc_7170_; 
v_reuseFailAlloc_7170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7170_, 0, v___x_7160_);
lean_ctor_set(v_reuseFailAlloc_7170_, 1, v_k_7101_);
lean_ctor_set(v_reuseFailAlloc_7170_, 2, v_v_7102_);
lean_ctor_set(v_reuseFailAlloc_7170_, 3, v_l_7103_);
lean_ctor_set(v_reuseFailAlloc_7170_, 4, v___x_7164_);
v___x_7169_ = v_reuseFailAlloc_7170_;
goto v_reusejp_7168_;
}
v_reusejp_7168_:
{
return v___x_7169_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7184_; 
v_l_7184_ = lean_ctor_get(v_impl_7097_, 3);
lean_inc(v_l_7184_);
if (lean_obj_tag(v_l_7184_) == 0)
{
lean_object* v_r_7185_; lean_object* v_k_7186_; lean_object* v_v_7187_; lean_object* v___x_7189_; uint8_t v_isShared_7190_; uint8_t v_isSharedCheck_7198_; 
v_r_7185_ = lean_ctor_get(v_impl_7097_, 4);
v_k_7186_ = lean_ctor_get(v_impl_7097_, 1);
v_v_7187_ = lean_ctor_get(v_impl_7097_, 2);
v_isSharedCheck_7198_ = !lean_is_exclusive(v_impl_7097_);
if (v_isSharedCheck_7198_ == 0)
{
lean_object* v_unused_7199_; lean_object* v_unused_7200_; 
v_unused_7199_ = lean_ctor_get(v_impl_7097_, 3);
lean_dec(v_unused_7199_);
v_unused_7200_ = lean_ctor_get(v_impl_7097_, 0);
lean_dec(v_unused_7200_);
v___x_7189_ = v_impl_7097_;
v_isShared_7190_ = v_isSharedCheck_7198_;
goto v_resetjp_7188_;
}
else
{
lean_inc(v_r_7185_);
lean_inc(v_v_7187_);
lean_inc(v_k_7186_);
lean_dec(v_impl_7097_);
v___x_7189_ = lean_box(0);
v_isShared_7190_ = v_isSharedCheck_7198_;
goto v_resetjp_7188_;
}
v_resetjp_7188_:
{
lean_object* v___x_7191_; lean_object* v___x_7193_; 
v___x_7191_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7185_);
if (v_isShared_7190_ == 0)
{
lean_ctor_set(v___x_7189_, 3, v_r_7185_);
lean_ctor_set(v___x_7189_, 2, v_v_7090_);
lean_ctor_set(v___x_7189_, 1, v_k_7089_);
lean_ctor_set(v___x_7189_, 0, v___x_7098_);
v___x_7193_ = v___x_7189_;
goto v_reusejp_7192_;
}
else
{
lean_object* v_reuseFailAlloc_7197_; 
v_reuseFailAlloc_7197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7197_, 0, v___x_7098_);
lean_ctor_set(v_reuseFailAlloc_7197_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7197_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7197_, 3, v_r_7185_);
lean_ctor_set(v_reuseFailAlloc_7197_, 4, v_r_7185_);
v___x_7193_ = v_reuseFailAlloc_7197_;
goto v_reusejp_7192_;
}
v_reusejp_7192_:
{
lean_object* v___x_7195_; 
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v___x_7193_);
lean_ctor_set(v___x_7094_, 3, v_l_7184_);
lean_ctor_set(v___x_7094_, 2, v_v_7187_);
lean_ctor_set(v___x_7094_, 1, v_k_7186_);
lean_ctor_set(v___x_7094_, 0, v___x_7191_);
v___x_7195_ = v___x_7094_;
goto v_reusejp_7194_;
}
else
{
lean_object* v_reuseFailAlloc_7196_; 
v_reuseFailAlloc_7196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7196_, 0, v___x_7191_);
lean_ctor_set(v_reuseFailAlloc_7196_, 1, v_k_7186_);
lean_ctor_set(v_reuseFailAlloc_7196_, 2, v_v_7187_);
lean_ctor_set(v_reuseFailAlloc_7196_, 3, v_l_7184_);
lean_ctor_set(v_reuseFailAlloc_7196_, 4, v___x_7193_);
v___x_7195_ = v_reuseFailAlloc_7196_;
goto v_reusejp_7194_;
}
v_reusejp_7194_:
{
return v___x_7195_;
}
}
}
}
else
{
lean_object* v_r_7201_; 
v_r_7201_ = lean_ctor_get(v_impl_7097_, 4);
lean_inc(v_r_7201_);
if (lean_obj_tag(v_r_7201_) == 0)
{
lean_object* v_k_7202_; lean_object* v_v_7203_; lean_object* v___x_7205_; uint8_t v_isShared_7206_; uint8_t v_isSharedCheck_7226_; 
v_k_7202_ = lean_ctor_get(v_impl_7097_, 1);
v_v_7203_ = lean_ctor_get(v_impl_7097_, 2);
v_isSharedCheck_7226_ = !lean_is_exclusive(v_impl_7097_);
if (v_isSharedCheck_7226_ == 0)
{
lean_object* v_unused_7227_; lean_object* v_unused_7228_; lean_object* v_unused_7229_; 
v_unused_7227_ = lean_ctor_get(v_impl_7097_, 4);
lean_dec(v_unused_7227_);
v_unused_7228_ = lean_ctor_get(v_impl_7097_, 3);
lean_dec(v_unused_7228_);
v_unused_7229_ = lean_ctor_get(v_impl_7097_, 0);
lean_dec(v_unused_7229_);
v___x_7205_ = v_impl_7097_;
v_isShared_7206_ = v_isSharedCheck_7226_;
goto v_resetjp_7204_;
}
else
{
lean_inc(v_v_7203_);
lean_inc(v_k_7202_);
lean_dec(v_impl_7097_);
v___x_7205_ = lean_box(0);
v_isShared_7206_ = v_isSharedCheck_7226_;
goto v_resetjp_7204_;
}
v_resetjp_7204_:
{
lean_object* v_k_7207_; lean_object* v_v_7208_; lean_object* v___x_7210_; uint8_t v_isShared_7211_; uint8_t v_isSharedCheck_7222_; 
v_k_7207_ = lean_ctor_get(v_r_7201_, 1);
v_v_7208_ = lean_ctor_get(v_r_7201_, 2);
v_isSharedCheck_7222_ = !lean_is_exclusive(v_r_7201_);
if (v_isSharedCheck_7222_ == 0)
{
lean_object* v_unused_7223_; lean_object* v_unused_7224_; lean_object* v_unused_7225_; 
v_unused_7223_ = lean_ctor_get(v_r_7201_, 4);
lean_dec(v_unused_7223_);
v_unused_7224_ = lean_ctor_get(v_r_7201_, 3);
lean_dec(v_unused_7224_);
v_unused_7225_ = lean_ctor_get(v_r_7201_, 0);
lean_dec(v_unused_7225_);
v___x_7210_ = v_r_7201_;
v_isShared_7211_ = v_isSharedCheck_7222_;
goto v_resetjp_7209_;
}
else
{
lean_inc(v_v_7208_);
lean_inc(v_k_7207_);
lean_dec(v_r_7201_);
v___x_7210_ = lean_box(0);
v_isShared_7211_ = v_isSharedCheck_7222_;
goto v_resetjp_7209_;
}
v_resetjp_7209_:
{
lean_object* v___x_7212_; lean_object* v___x_7214_; 
v___x_7212_ = lean_unsigned_to_nat(3u);
if (v_isShared_7211_ == 0)
{
lean_ctor_set(v___x_7210_, 4, v_l_7184_);
lean_ctor_set(v___x_7210_, 3, v_l_7184_);
lean_ctor_set(v___x_7210_, 2, v_v_7203_);
lean_ctor_set(v___x_7210_, 1, v_k_7202_);
lean_ctor_set(v___x_7210_, 0, v___x_7098_);
v___x_7214_ = v___x_7210_;
goto v_reusejp_7213_;
}
else
{
lean_object* v_reuseFailAlloc_7221_; 
v_reuseFailAlloc_7221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7221_, 0, v___x_7098_);
lean_ctor_set(v_reuseFailAlloc_7221_, 1, v_k_7202_);
lean_ctor_set(v_reuseFailAlloc_7221_, 2, v_v_7203_);
lean_ctor_set(v_reuseFailAlloc_7221_, 3, v_l_7184_);
lean_ctor_set(v_reuseFailAlloc_7221_, 4, v_l_7184_);
v___x_7214_ = v_reuseFailAlloc_7221_;
goto v_reusejp_7213_;
}
v_reusejp_7213_:
{
lean_object* v___x_7216_; 
if (v_isShared_7206_ == 0)
{
lean_ctor_set(v___x_7205_, 4, v_l_7184_);
lean_ctor_set(v___x_7205_, 2, v_v_7090_);
lean_ctor_set(v___x_7205_, 1, v_k_7089_);
lean_ctor_set(v___x_7205_, 0, v___x_7098_);
v___x_7216_ = v___x_7205_;
goto v_reusejp_7215_;
}
else
{
lean_object* v_reuseFailAlloc_7220_; 
v_reuseFailAlloc_7220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7220_, 0, v___x_7098_);
lean_ctor_set(v_reuseFailAlloc_7220_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7220_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7220_, 3, v_l_7184_);
lean_ctor_set(v_reuseFailAlloc_7220_, 4, v_l_7184_);
v___x_7216_ = v_reuseFailAlloc_7220_;
goto v_reusejp_7215_;
}
v_reusejp_7215_:
{
lean_object* v___x_7218_; 
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v___x_7216_);
lean_ctor_set(v___x_7094_, 3, v___x_7214_);
lean_ctor_set(v___x_7094_, 2, v_v_7208_);
lean_ctor_set(v___x_7094_, 1, v_k_7207_);
lean_ctor_set(v___x_7094_, 0, v___x_7212_);
v___x_7218_ = v___x_7094_;
goto v_reusejp_7217_;
}
else
{
lean_object* v_reuseFailAlloc_7219_; 
v_reuseFailAlloc_7219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7219_, 0, v___x_7212_);
lean_ctor_set(v_reuseFailAlloc_7219_, 1, v_k_7207_);
lean_ctor_set(v_reuseFailAlloc_7219_, 2, v_v_7208_);
lean_ctor_set(v_reuseFailAlloc_7219_, 3, v___x_7214_);
lean_ctor_set(v_reuseFailAlloc_7219_, 4, v___x_7216_);
v___x_7218_ = v_reuseFailAlloc_7219_;
goto v_reusejp_7217_;
}
v_reusejp_7217_:
{
return v___x_7218_;
}
}
}
}
}
}
else
{
lean_object* v___x_7230_; lean_object* v___x_7232_; 
v___x_7230_ = lean_unsigned_to_nat(2u);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_r_7201_);
lean_ctor_set(v___x_7094_, 3, v_impl_7097_);
lean_ctor_set(v___x_7094_, 0, v___x_7230_);
v___x_7232_ = v___x_7094_;
goto v_reusejp_7231_;
}
else
{
lean_object* v_reuseFailAlloc_7233_; 
v_reuseFailAlloc_7233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7233_, 0, v___x_7230_);
lean_ctor_set(v_reuseFailAlloc_7233_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7233_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7233_, 3, v_impl_7097_);
lean_ctor_set(v_reuseFailAlloc_7233_, 4, v_r_7201_);
v___x_7232_ = v_reuseFailAlloc_7233_;
goto v_reusejp_7231_;
}
v_reusejp_7231_:
{
return v___x_7232_;
}
}
}
}
}
case 1:
{
lean_object* v___x_7235_; 
lean_dec(v_v_7090_);
lean_dec(v_k_7089_);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 2, v_v_7086_);
lean_ctor_set(v___x_7094_, 1, v_k_7085_);
v___x_7235_ = v___x_7094_;
goto v_reusejp_7234_;
}
else
{
lean_object* v_reuseFailAlloc_7236_; 
v_reuseFailAlloc_7236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7236_, 0, v_size_7088_);
lean_ctor_set(v_reuseFailAlloc_7236_, 1, v_k_7085_);
lean_ctor_set(v_reuseFailAlloc_7236_, 2, v_v_7086_);
lean_ctor_set(v_reuseFailAlloc_7236_, 3, v_l_7091_);
lean_ctor_set(v_reuseFailAlloc_7236_, 4, v_r_7092_);
v___x_7235_ = v_reuseFailAlloc_7236_;
goto v_reusejp_7234_;
}
v_reusejp_7234_:
{
return v___x_7235_;
}
}
default: 
{
lean_object* v_impl_7237_; lean_object* v___x_7238_; 
lean_dec(v_size_7088_);
v_impl_7237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7085_, v_v_7086_, v_r_7092_);
v___x_7238_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7091_) == 0)
{
lean_object* v_size_7239_; lean_object* v_size_7240_; lean_object* v_k_7241_; lean_object* v_v_7242_; lean_object* v_l_7243_; lean_object* v_r_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; uint8_t v___x_7247_; 
v_size_7239_ = lean_ctor_get(v_l_7091_, 0);
v_size_7240_ = lean_ctor_get(v_impl_7237_, 0);
lean_inc(v_size_7240_);
v_k_7241_ = lean_ctor_get(v_impl_7237_, 1);
lean_inc(v_k_7241_);
v_v_7242_ = lean_ctor_get(v_impl_7237_, 2);
lean_inc(v_v_7242_);
v_l_7243_ = lean_ctor_get(v_impl_7237_, 3);
lean_inc(v_l_7243_);
v_r_7244_ = lean_ctor_get(v_impl_7237_, 4);
lean_inc(v_r_7244_);
v___x_7245_ = lean_unsigned_to_nat(3u);
v___x_7246_ = lean_nat_mul(v___x_7245_, v_size_7239_);
v___x_7247_ = lean_nat_dec_lt(v___x_7246_, v_size_7240_);
lean_dec(v___x_7246_);
if (v___x_7247_ == 0)
{
lean_object* v___x_7248_; lean_object* v___x_7249_; lean_object* v___x_7251_; 
lean_dec(v_r_7244_);
lean_dec(v_l_7243_);
lean_dec(v_v_7242_);
lean_dec(v_k_7241_);
v___x_7248_ = lean_nat_add(v___x_7238_, v_size_7239_);
v___x_7249_ = lean_nat_add(v___x_7248_, v_size_7240_);
lean_dec(v_size_7240_);
lean_dec(v___x_7248_);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_impl_7237_);
lean_ctor_set(v___x_7094_, 0, v___x_7249_);
v___x_7251_ = v___x_7094_;
goto v_reusejp_7250_;
}
else
{
lean_object* v_reuseFailAlloc_7252_; 
v_reuseFailAlloc_7252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7252_, 0, v___x_7249_);
lean_ctor_set(v_reuseFailAlloc_7252_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7252_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7252_, 3, v_l_7091_);
lean_ctor_set(v_reuseFailAlloc_7252_, 4, v_impl_7237_);
v___x_7251_ = v_reuseFailAlloc_7252_;
goto v_reusejp_7250_;
}
v_reusejp_7250_:
{
return v___x_7251_;
}
}
else
{
lean_object* v___x_7254_; uint8_t v_isShared_7255_; uint8_t v_isSharedCheck_7316_; 
v_isSharedCheck_7316_ = !lean_is_exclusive(v_impl_7237_);
if (v_isSharedCheck_7316_ == 0)
{
lean_object* v_unused_7317_; lean_object* v_unused_7318_; lean_object* v_unused_7319_; lean_object* v_unused_7320_; lean_object* v_unused_7321_; 
v_unused_7317_ = lean_ctor_get(v_impl_7237_, 4);
lean_dec(v_unused_7317_);
v_unused_7318_ = lean_ctor_get(v_impl_7237_, 3);
lean_dec(v_unused_7318_);
v_unused_7319_ = lean_ctor_get(v_impl_7237_, 2);
lean_dec(v_unused_7319_);
v_unused_7320_ = lean_ctor_get(v_impl_7237_, 1);
lean_dec(v_unused_7320_);
v_unused_7321_ = lean_ctor_get(v_impl_7237_, 0);
lean_dec(v_unused_7321_);
v___x_7254_ = v_impl_7237_;
v_isShared_7255_ = v_isSharedCheck_7316_;
goto v_resetjp_7253_;
}
else
{
lean_dec(v_impl_7237_);
v___x_7254_ = lean_box(0);
v_isShared_7255_ = v_isSharedCheck_7316_;
goto v_resetjp_7253_;
}
v_resetjp_7253_:
{
lean_object* v_size_7256_; lean_object* v_k_7257_; lean_object* v_v_7258_; lean_object* v_l_7259_; lean_object* v_r_7260_; lean_object* v_size_7261_; lean_object* v___x_7262_; lean_object* v___x_7263_; uint8_t v___x_7264_; 
v_size_7256_ = lean_ctor_get(v_l_7243_, 0);
v_k_7257_ = lean_ctor_get(v_l_7243_, 1);
v_v_7258_ = lean_ctor_get(v_l_7243_, 2);
v_l_7259_ = lean_ctor_get(v_l_7243_, 3);
v_r_7260_ = lean_ctor_get(v_l_7243_, 4);
v_size_7261_ = lean_ctor_get(v_r_7244_, 0);
v___x_7262_ = lean_unsigned_to_nat(2u);
v___x_7263_ = lean_nat_mul(v___x_7262_, v_size_7261_);
v___x_7264_ = lean_nat_dec_lt(v_size_7256_, v___x_7263_);
lean_dec(v___x_7263_);
if (v___x_7264_ == 0)
{
lean_object* v___x_7266_; uint8_t v_isShared_7267_; uint8_t v_isSharedCheck_7292_; 
lean_inc(v_r_7260_);
lean_inc(v_l_7259_);
lean_inc(v_v_7258_);
lean_inc(v_k_7257_);
v_isSharedCheck_7292_ = !lean_is_exclusive(v_l_7243_);
if (v_isSharedCheck_7292_ == 0)
{
lean_object* v_unused_7293_; lean_object* v_unused_7294_; lean_object* v_unused_7295_; lean_object* v_unused_7296_; lean_object* v_unused_7297_; 
v_unused_7293_ = lean_ctor_get(v_l_7243_, 4);
lean_dec(v_unused_7293_);
v_unused_7294_ = lean_ctor_get(v_l_7243_, 3);
lean_dec(v_unused_7294_);
v_unused_7295_ = lean_ctor_get(v_l_7243_, 2);
lean_dec(v_unused_7295_);
v_unused_7296_ = lean_ctor_get(v_l_7243_, 1);
lean_dec(v_unused_7296_);
v_unused_7297_ = lean_ctor_get(v_l_7243_, 0);
lean_dec(v_unused_7297_);
v___x_7266_ = v_l_7243_;
v_isShared_7267_ = v_isSharedCheck_7292_;
goto v_resetjp_7265_;
}
else
{
lean_dec(v_l_7243_);
v___x_7266_ = lean_box(0);
v_isShared_7267_ = v_isSharedCheck_7292_;
goto v_resetjp_7265_;
}
v_resetjp_7265_:
{
lean_object* v___x_7268_; lean_object* v___x_7269_; lean_object* v___y_7271_; lean_object* v___y_7272_; lean_object* v___y_7273_; lean_object* v___y_7282_; 
v___x_7268_ = lean_nat_add(v___x_7238_, v_size_7239_);
v___x_7269_ = lean_nat_add(v___x_7268_, v_size_7240_);
lean_dec(v_size_7240_);
if (lean_obj_tag(v_l_7259_) == 0)
{
lean_object* v_size_7290_; 
v_size_7290_ = lean_ctor_get(v_l_7259_, 0);
lean_inc(v_size_7290_);
v___y_7282_ = v_size_7290_;
goto v___jp_7281_;
}
else
{
lean_object* v___x_7291_; 
v___x_7291_ = lean_unsigned_to_nat(0u);
v___y_7282_ = v___x_7291_;
goto v___jp_7281_;
}
v___jp_7270_:
{
lean_object* v___x_7274_; lean_object* v___x_7276_; 
v___x_7274_ = lean_nat_add(v___y_7272_, v___y_7273_);
lean_dec(v___y_7273_);
lean_dec(v___y_7272_);
if (v_isShared_7267_ == 0)
{
lean_ctor_set(v___x_7266_, 4, v_r_7244_);
lean_ctor_set(v___x_7266_, 3, v_r_7260_);
lean_ctor_set(v___x_7266_, 2, v_v_7242_);
lean_ctor_set(v___x_7266_, 1, v_k_7241_);
lean_ctor_set(v___x_7266_, 0, v___x_7274_);
v___x_7276_ = v___x_7266_;
goto v_reusejp_7275_;
}
else
{
lean_object* v_reuseFailAlloc_7280_; 
v_reuseFailAlloc_7280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7280_, 0, v___x_7274_);
lean_ctor_set(v_reuseFailAlloc_7280_, 1, v_k_7241_);
lean_ctor_set(v_reuseFailAlloc_7280_, 2, v_v_7242_);
lean_ctor_set(v_reuseFailAlloc_7280_, 3, v_r_7260_);
lean_ctor_set(v_reuseFailAlloc_7280_, 4, v_r_7244_);
v___x_7276_ = v_reuseFailAlloc_7280_;
goto v_reusejp_7275_;
}
v_reusejp_7275_:
{
lean_object* v___x_7278_; 
if (v_isShared_7255_ == 0)
{
lean_ctor_set(v___x_7254_, 4, v___x_7276_);
lean_ctor_set(v___x_7254_, 3, v___y_7271_);
lean_ctor_set(v___x_7254_, 2, v_v_7258_);
lean_ctor_set(v___x_7254_, 1, v_k_7257_);
lean_ctor_set(v___x_7254_, 0, v___x_7269_);
v___x_7278_ = v___x_7254_;
goto v_reusejp_7277_;
}
else
{
lean_object* v_reuseFailAlloc_7279_; 
v_reuseFailAlloc_7279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7279_, 0, v___x_7269_);
lean_ctor_set(v_reuseFailAlloc_7279_, 1, v_k_7257_);
lean_ctor_set(v_reuseFailAlloc_7279_, 2, v_v_7258_);
lean_ctor_set(v_reuseFailAlloc_7279_, 3, v___y_7271_);
lean_ctor_set(v_reuseFailAlloc_7279_, 4, v___x_7276_);
v___x_7278_ = v_reuseFailAlloc_7279_;
goto v_reusejp_7277_;
}
v_reusejp_7277_:
{
return v___x_7278_;
}
}
}
v___jp_7281_:
{
lean_object* v___x_7283_; lean_object* v___x_7285_; 
v___x_7283_ = lean_nat_add(v___x_7268_, v___y_7282_);
lean_dec(v___y_7282_);
lean_dec(v___x_7268_);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_l_7259_);
lean_ctor_set(v___x_7094_, 0, v___x_7283_);
v___x_7285_ = v___x_7094_;
goto v_reusejp_7284_;
}
else
{
lean_object* v_reuseFailAlloc_7289_; 
v_reuseFailAlloc_7289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7289_, 0, v___x_7283_);
lean_ctor_set(v_reuseFailAlloc_7289_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7289_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7289_, 3, v_l_7091_);
lean_ctor_set(v_reuseFailAlloc_7289_, 4, v_l_7259_);
v___x_7285_ = v_reuseFailAlloc_7289_;
goto v_reusejp_7284_;
}
v_reusejp_7284_:
{
lean_object* v___x_7286_; 
v___x_7286_ = lean_nat_add(v___x_7238_, v_size_7261_);
if (lean_obj_tag(v_r_7260_) == 0)
{
lean_object* v_size_7287_; 
v_size_7287_ = lean_ctor_get(v_r_7260_, 0);
lean_inc(v_size_7287_);
v___y_7271_ = v___x_7285_;
v___y_7272_ = v___x_7286_;
v___y_7273_ = v_size_7287_;
goto v___jp_7270_;
}
else
{
lean_object* v___x_7288_; 
v___x_7288_ = lean_unsigned_to_nat(0u);
v___y_7271_ = v___x_7285_;
v___y_7272_ = v___x_7286_;
v___y_7273_ = v___x_7288_;
goto v___jp_7270_;
}
}
}
}
}
else
{
lean_object* v___x_7298_; lean_object* v___x_7299_; lean_object* v___x_7300_; lean_object* v___x_7302_; 
lean_del_object(v___x_7094_);
v___x_7298_ = lean_nat_add(v___x_7238_, v_size_7239_);
v___x_7299_ = lean_nat_add(v___x_7298_, v_size_7240_);
lean_dec(v_size_7240_);
v___x_7300_ = lean_nat_add(v___x_7298_, v_size_7256_);
lean_dec(v___x_7298_);
lean_inc_ref(v_l_7091_);
if (v_isShared_7255_ == 0)
{
lean_ctor_set(v___x_7254_, 4, v_l_7243_);
lean_ctor_set(v___x_7254_, 3, v_l_7091_);
lean_ctor_set(v___x_7254_, 2, v_v_7090_);
lean_ctor_set(v___x_7254_, 1, v_k_7089_);
lean_ctor_set(v___x_7254_, 0, v___x_7300_);
v___x_7302_ = v___x_7254_;
goto v_reusejp_7301_;
}
else
{
lean_object* v_reuseFailAlloc_7315_; 
v_reuseFailAlloc_7315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7315_, 0, v___x_7300_);
lean_ctor_set(v_reuseFailAlloc_7315_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7315_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7315_, 3, v_l_7091_);
lean_ctor_set(v_reuseFailAlloc_7315_, 4, v_l_7243_);
v___x_7302_ = v_reuseFailAlloc_7315_;
goto v_reusejp_7301_;
}
v_reusejp_7301_:
{
lean_object* v___x_7304_; uint8_t v_isShared_7305_; uint8_t v_isSharedCheck_7309_; 
v_isSharedCheck_7309_ = !lean_is_exclusive(v_l_7091_);
if (v_isSharedCheck_7309_ == 0)
{
lean_object* v_unused_7310_; lean_object* v_unused_7311_; lean_object* v_unused_7312_; lean_object* v_unused_7313_; lean_object* v_unused_7314_; 
v_unused_7310_ = lean_ctor_get(v_l_7091_, 4);
lean_dec(v_unused_7310_);
v_unused_7311_ = lean_ctor_get(v_l_7091_, 3);
lean_dec(v_unused_7311_);
v_unused_7312_ = lean_ctor_get(v_l_7091_, 2);
lean_dec(v_unused_7312_);
v_unused_7313_ = lean_ctor_get(v_l_7091_, 1);
lean_dec(v_unused_7313_);
v_unused_7314_ = lean_ctor_get(v_l_7091_, 0);
lean_dec(v_unused_7314_);
v___x_7304_ = v_l_7091_;
v_isShared_7305_ = v_isSharedCheck_7309_;
goto v_resetjp_7303_;
}
else
{
lean_dec(v_l_7091_);
v___x_7304_ = lean_box(0);
v_isShared_7305_ = v_isSharedCheck_7309_;
goto v_resetjp_7303_;
}
v_resetjp_7303_:
{
lean_object* v___x_7307_; 
if (v_isShared_7305_ == 0)
{
lean_ctor_set(v___x_7304_, 4, v_r_7244_);
lean_ctor_set(v___x_7304_, 3, v___x_7302_);
lean_ctor_set(v___x_7304_, 2, v_v_7242_);
lean_ctor_set(v___x_7304_, 1, v_k_7241_);
lean_ctor_set(v___x_7304_, 0, v___x_7299_);
v___x_7307_ = v___x_7304_;
goto v_reusejp_7306_;
}
else
{
lean_object* v_reuseFailAlloc_7308_; 
v_reuseFailAlloc_7308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7308_, 0, v___x_7299_);
lean_ctor_set(v_reuseFailAlloc_7308_, 1, v_k_7241_);
lean_ctor_set(v_reuseFailAlloc_7308_, 2, v_v_7242_);
lean_ctor_set(v_reuseFailAlloc_7308_, 3, v___x_7302_);
lean_ctor_set(v_reuseFailAlloc_7308_, 4, v_r_7244_);
v___x_7307_ = v_reuseFailAlloc_7308_;
goto v_reusejp_7306_;
}
v_reusejp_7306_:
{
return v___x_7307_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7322_; 
v_l_7322_ = lean_ctor_get(v_impl_7237_, 3);
lean_inc(v_l_7322_);
if (lean_obj_tag(v_l_7322_) == 0)
{
lean_object* v_r_7323_; lean_object* v_k_7324_; lean_object* v_v_7325_; lean_object* v___x_7327_; uint8_t v_isShared_7328_; uint8_t v_isSharedCheck_7348_; 
v_r_7323_ = lean_ctor_get(v_impl_7237_, 4);
v_k_7324_ = lean_ctor_get(v_impl_7237_, 1);
v_v_7325_ = lean_ctor_get(v_impl_7237_, 2);
v_isSharedCheck_7348_ = !lean_is_exclusive(v_impl_7237_);
if (v_isSharedCheck_7348_ == 0)
{
lean_object* v_unused_7349_; lean_object* v_unused_7350_; 
v_unused_7349_ = lean_ctor_get(v_impl_7237_, 3);
lean_dec(v_unused_7349_);
v_unused_7350_ = lean_ctor_get(v_impl_7237_, 0);
lean_dec(v_unused_7350_);
v___x_7327_ = v_impl_7237_;
v_isShared_7328_ = v_isSharedCheck_7348_;
goto v_resetjp_7326_;
}
else
{
lean_inc(v_r_7323_);
lean_inc(v_v_7325_);
lean_inc(v_k_7324_);
lean_dec(v_impl_7237_);
v___x_7327_ = lean_box(0);
v_isShared_7328_ = v_isSharedCheck_7348_;
goto v_resetjp_7326_;
}
v_resetjp_7326_:
{
lean_object* v_k_7329_; lean_object* v_v_7330_; lean_object* v___x_7332_; uint8_t v_isShared_7333_; uint8_t v_isSharedCheck_7344_; 
v_k_7329_ = lean_ctor_get(v_l_7322_, 1);
v_v_7330_ = lean_ctor_get(v_l_7322_, 2);
v_isSharedCheck_7344_ = !lean_is_exclusive(v_l_7322_);
if (v_isSharedCheck_7344_ == 0)
{
lean_object* v_unused_7345_; lean_object* v_unused_7346_; lean_object* v_unused_7347_; 
v_unused_7345_ = lean_ctor_get(v_l_7322_, 4);
lean_dec(v_unused_7345_);
v_unused_7346_ = lean_ctor_get(v_l_7322_, 3);
lean_dec(v_unused_7346_);
v_unused_7347_ = lean_ctor_get(v_l_7322_, 0);
lean_dec(v_unused_7347_);
v___x_7332_ = v_l_7322_;
v_isShared_7333_ = v_isSharedCheck_7344_;
goto v_resetjp_7331_;
}
else
{
lean_inc(v_v_7330_);
lean_inc(v_k_7329_);
lean_dec(v_l_7322_);
v___x_7332_ = lean_box(0);
v_isShared_7333_ = v_isSharedCheck_7344_;
goto v_resetjp_7331_;
}
v_resetjp_7331_:
{
lean_object* v___x_7334_; lean_object* v___x_7336_; 
v___x_7334_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7323_, 2);
if (v_isShared_7333_ == 0)
{
lean_ctor_set(v___x_7332_, 4, v_r_7323_);
lean_ctor_set(v___x_7332_, 3, v_r_7323_);
lean_ctor_set(v___x_7332_, 2, v_v_7090_);
lean_ctor_set(v___x_7332_, 1, v_k_7089_);
lean_ctor_set(v___x_7332_, 0, v___x_7238_);
v___x_7336_ = v___x_7332_;
goto v_reusejp_7335_;
}
else
{
lean_object* v_reuseFailAlloc_7343_; 
v_reuseFailAlloc_7343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7343_, 0, v___x_7238_);
lean_ctor_set(v_reuseFailAlloc_7343_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7343_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7343_, 3, v_r_7323_);
lean_ctor_set(v_reuseFailAlloc_7343_, 4, v_r_7323_);
v___x_7336_ = v_reuseFailAlloc_7343_;
goto v_reusejp_7335_;
}
v_reusejp_7335_:
{
lean_object* v___x_7338_; 
lean_inc(v_r_7323_);
if (v_isShared_7328_ == 0)
{
lean_ctor_set(v___x_7327_, 3, v_r_7323_);
lean_ctor_set(v___x_7327_, 0, v___x_7238_);
v___x_7338_ = v___x_7327_;
goto v_reusejp_7337_;
}
else
{
lean_object* v_reuseFailAlloc_7342_; 
v_reuseFailAlloc_7342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7342_, 0, v___x_7238_);
lean_ctor_set(v_reuseFailAlloc_7342_, 1, v_k_7324_);
lean_ctor_set(v_reuseFailAlloc_7342_, 2, v_v_7325_);
lean_ctor_set(v_reuseFailAlloc_7342_, 3, v_r_7323_);
lean_ctor_set(v_reuseFailAlloc_7342_, 4, v_r_7323_);
v___x_7338_ = v_reuseFailAlloc_7342_;
goto v_reusejp_7337_;
}
v_reusejp_7337_:
{
lean_object* v___x_7340_; 
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v___x_7338_);
lean_ctor_set(v___x_7094_, 3, v___x_7336_);
lean_ctor_set(v___x_7094_, 2, v_v_7330_);
lean_ctor_set(v___x_7094_, 1, v_k_7329_);
lean_ctor_set(v___x_7094_, 0, v___x_7334_);
v___x_7340_ = v___x_7094_;
goto v_reusejp_7339_;
}
else
{
lean_object* v_reuseFailAlloc_7341_; 
v_reuseFailAlloc_7341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7341_, 0, v___x_7334_);
lean_ctor_set(v_reuseFailAlloc_7341_, 1, v_k_7329_);
lean_ctor_set(v_reuseFailAlloc_7341_, 2, v_v_7330_);
lean_ctor_set(v_reuseFailAlloc_7341_, 3, v___x_7336_);
lean_ctor_set(v_reuseFailAlloc_7341_, 4, v___x_7338_);
v___x_7340_ = v_reuseFailAlloc_7341_;
goto v_reusejp_7339_;
}
v_reusejp_7339_:
{
return v___x_7340_;
}
}
}
}
}
}
else
{
lean_object* v_r_7351_; 
v_r_7351_ = lean_ctor_get(v_impl_7237_, 4);
lean_inc(v_r_7351_);
if (lean_obj_tag(v_r_7351_) == 0)
{
lean_object* v_k_7352_; lean_object* v_v_7353_; lean_object* v___x_7355_; uint8_t v_isShared_7356_; uint8_t v_isSharedCheck_7364_; 
v_k_7352_ = lean_ctor_get(v_impl_7237_, 1);
v_v_7353_ = lean_ctor_get(v_impl_7237_, 2);
v_isSharedCheck_7364_ = !lean_is_exclusive(v_impl_7237_);
if (v_isSharedCheck_7364_ == 0)
{
lean_object* v_unused_7365_; lean_object* v_unused_7366_; lean_object* v_unused_7367_; 
v_unused_7365_ = lean_ctor_get(v_impl_7237_, 4);
lean_dec(v_unused_7365_);
v_unused_7366_ = lean_ctor_get(v_impl_7237_, 3);
lean_dec(v_unused_7366_);
v_unused_7367_ = lean_ctor_get(v_impl_7237_, 0);
lean_dec(v_unused_7367_);
v___x_7355_ = v_impl_7237_;
v_isShared_7356_ = v_isSharedCheck_7364_;
goto v_resetjp_7354_;
}
else
{
lean_inc(v_v_7353_);
lean_inc(v_k_7352_);
lean_dec(v_impl_7237_);
v___x_7355_ = lean_box(0);
v_isShared_7356_ = v_isSharedCheck_7364_;
goto v_resetjp_7354_;
}
v_resetjp_7354_:
{
lean_object* v___x_7357_; lean_object* v___x_7359_; 
v___x_7357_ = lean_unsigned_to_nat(3u);
if (v_isShared_7356_ == 0)
{
lean_ctor_set(v___x_7355_, 4, v_l_7322_);
lean_ctor_set(v___x_7355_, 2, v_v_7090_);
lean_ctor_set(v___x_7355_, 1, v_k_7089_);
lean_ctor_set(v___x_7355_, 0, v___x_7238_);
v___x_7359_ = v___x_7355_;
goto v_reusejp_7358_;
}
else
{
lean_object* v_reuseFailAlloc_7363_; 
v_reuseFailAlloc_7363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7363_, 0, v___x_7238_);
lean_ctor_set(v_reuseFailAlloc_7363_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7363_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7363_, 3, v_l_7322_);
lean_ctor_set(v_reuseFailAlloc_7363_, 4, v_l_7322_);
v___x_7359_ = v_reuseFailAlloc_7363_;
goto v_reusejp_7358_;
}
v_reusejp_7358_:
{
lean_object* v___x_7361_; 
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_r_7351_);
lean_ctor_set(v___x_7094_, 3, v___x_7359_);
lean_ctor_set(v___x_7094_, 2, v_v_7353_);
lean_ctor_set(v___x_7094_, 1, v_k_7352_);
lean_ctor_set(v___x_7094_, 0, v___x_7357_);
v___x_7361_ = v___x_7094_;
goto v_reusejp_7360_;
}
else
{
lean_object* v_reuseFailAlloc_7362_; 
v_reuseFailAlloc_7362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7362_, 0, v___x_7357_);
lean_ctor_set(v_reuseFailAlloc_7362_, 1, v_k_7352_);
lean_ctor_set(v_reuseFailAlloc_7362_, 2, v_v_7353_);
lean_ctor_set(v_reuseFailAlloc_7362_, 3, v___x_7359_);
lean_ctor_set(v_reuseFailAlloc_7362_, 4, v_r_7351_);
v___x_7361_ = v_reuseFailAlloc_7362_;
goto v_reusejp_7360_;
}
v_reusejp_7360_:
{
return v___x_7361_;
}
}
}
}
else
{
lean_object* v___x_7368_; lean_object* v___x_7370_; 
v___x_7368_ = lean_unsigned_to_nat(2u);
if (v_isShared_7095_ == 0)
{
lean_ctor_set(v___x_7094_, 4, v_impl_7237_);
lean_ctor_set(v___x_7094_, 3, v_r_7351_);
lean_ctor_set(v___x_7094_, 0, v___x_7368_);
v___x_7370_ = v___x_7094_;
goto v_reusejp_7369_;
}
else
{
lean_object* v_reuseFailAlloc_7371_; 
v_reuseFailAlloc_7371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7371_, 0, v___x_7368_);
lean_ctor_set(v_reuseFailAlloc_7371_, 1, v_k_7089_);
lean_ctor_set(v_reuseFailAlloc_7371_, 2, v_v_7090_);
lean_ctor_set(v_reuseFailAlloc_7371_, 3, v_r_7351_);
lean_ctor_set(v_reuseFailAlloc_7371_, 4, v_impl_7237_);
v___x_7370_ = v_reuseFailAlloc_7371_;
goto v_reusejp_7369_;
}
v_reusejp_7369_:
{
return v___x_7370_;
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
lean_object* v___x_7373_; lean_object* v___x_7374_; 
v___x_7373_ = lean_unsigned_to_nat(1u);
v___x_7374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7374_, 0, v___x_7373_);
lean_ctor_set(v___x_7374_, 1, v_k_7085_);
lean_ctor_set(v___x_7374_, 2, v_v_7086_);
lean_ctor_set(v___x_7374_, 3, v_t_7087_);
lean_ctor_set(v___x_7374_, 4, v_t_7087_);
return v___x_7374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7375_, lean_object* v_ps_7376_, lean_object* v_v_7377_, lean_object* v_o_7378_){
_start:
{
lean_object* v_name_7379_; lean_object* v_deps_7380_; lean_object* v_o_7381_; uint8_t v___x_7382_; 
v_name_7379_ = lean_ctor_get(v_lib_7375_, 1);
lean_inc_ref(v_name_7379_);
v_deps_7380_ = lean_ctor_get(v_lib_7375_, 2);
lean_inc_ref(v_deps_7380_);
v_o_7381_ = lean_array_push(v_o_7378_, v_lib_7375_);
v___x_7382_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7379_, v_v_7377_);
if (v___x_7382_ == 0)
{
uint8_t v___x_7383_; 
v___x_7383_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7379_, v_ps_7376_);
if (v___x_7383_ == 0)
{
lean_object* v_ps_7384_; lean_object* v___y_7386_; 
lean_inc_ref(v_name_7379_);
v_ps_7384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7384_, 0, v_name_7379_);
lean_ctor_set(v_ps_7384_, 1, v_ps_7376_);
if (v___x_7382_ == 0)
{
lean_object* v___x_7400_; lean_object* v___x_7401_; 
v___x_7400_ = lean_box(0);
v___x_7401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7379_, v___x_7400_, v_v_7377_);
v___y_7386_ = v___x_7401_;
goto v___jp_7385_;
}
else
{
lean_dec_ref(v_name_7379_);
v___y_7386_ = v_v_7377_;
goto v___jp_7385_;
}
v___jp_7385_:
{
lean_object* v___x_7387_; lean_object* v___x_7388_; lean_object* v___x_7389_; uint8_t v___x_7390_; 
v___x_7387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7387_, 0, v___y_7386_);
lean_ctor_set(v___x_7387_, 1, v_o_7381_);
v___x_7388_ = lean_unsigned_to_nat(0u);
v___x_7389_ = lean_array_get_size(v_deps_7380_);
v___x_7390_ = lean_nat_dec_lt(v___x_7388_, v___x_7389_);
if (v___x_7390_ == 0)
{
lean_object* v___x_7391_; 
lean_dec_ref_known(v_ps_7384_, 2);
lean_dec_ref(v_deps_7380_);
v___x_7391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7391_, 0, v___x_7387_);
return v___x_7391_;
}
else
{
uint8_t v___x_7392_; 
v___x_7392_ = lean_nat_dec_le(v___x_7389_, v___x_7389_);
if (v___x_7392_ == 0)
{
if (v___x_7390_ == 0)
{
lean_object* v___x_7393_; 
lean_dec_ref_known(v_ps_7384_, 2);
lean_dec_ref(v_deps_7380_);
v___x_7393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7393_, 0, v___x_7387_);
return v___x_7393_;
}
else
{
size_t v___x_7394_; size_t v___x_7395_; lean_object* v___x_7396_; 
v___x_7394_ = ((size_t)0ULL);
v___x_7395_ = lean_usize_of_nat(v___x_7389_);
v___x_7396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7384_, v_deps_7380_, v___x_7394_, v___x_7395_, v___x_7387_);
lean_dec_ref(v_deps_7380_);
return v___x_7396_;
}
}
else
{
size_t v___x_7397_; size_t v___x_7398_; lean_object* v___x_7399_; 
v___x_7397_ = ((size_t)0ULL);
v___x_7398_ = lean_usize_of_nat(v___x_7389_);
v___x_7399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7384_, v_deps_7380_, v___x_7397_, v___x_7398_, v___x_7387_);
lean_dec_ref(v_deps_7380_);
return v___x_7399_;
}
}
}
}
else
{
lean_object* v___x_7402_; lean_object* v___x_7403_; 
lean_dec_ref(v_o_7381_);
lean_dec_ref(v_deps_7380_);
lean_dec(v_v_7377_);
v___x_7402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7402_, 0, v_name_7379_);
lean_ctor_set(v___x_7402_, 1, v_ps_7376_);
v___x_7403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7403_, 0, v___x_7402_);
return v___x_7403_;
}
}
else
{
lean_object* v___x_7404_; lean_object* v___x_7405_; 
lean_dec_ref(v_deps_7380_);
lean_dec_ref(v_name_7379_);
lean_dec(v_ps_7376_);
v___x_7404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7404_, 0, v_v_7377_);
lean_ctor_set(v___x_7404_, 1, v_o_7381_);
v___x_7405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7405_, 0, v___x_7404_);
return v___x_7405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7406_, lean_object* v_as_7407_, size_t v_i_7408_, size_t v_stop_7409_, lean_object* v_b_7410_){
_start:
{
uint8_t v___x_7411_; 
v___x_7411_ = lean_usize_dec_eq(v_i_7408_, v_stop_7409_);
if (v___x_7411_ == 0)
{
lean_object* v_fst_7412_; lean_object* v_snd_7413_; lean_object* v___x_7414_; lean_object* v___x_7415_; 
v_fst_7412_ = lean_ctor_get(v_b_7410_, 0);
lean_inc(v_fst_7412_);
v_snd_7413_ = lean_ctor_get(v_b_7410_, 1);
lean_inc(v_snd_7413_);
lean_dec_ref(v_b_7410_);
v___x_7414_ = lean_array_uget_borrowed(v_as_7407_, v_i_7408_);
lean_inc(v_ps_7406_);
lean_inc(v___x_7414_);
v___x_7415_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7414_, v_ps_7406_, v_fst_7412_, v_snd_7413_);
if (lean_obj_tag(v___x_7415_) == 0)
{
lean_dec(v_ps_7406_);
return v___x_7415_;
}
else
{
lean_object* v_a_7416_; size_t v___x_7417_; size_t v___x_7418_; 
v_a_7416_ = lean_ctor_get(v___x_7415_, 0);
lean_inc(v_a_7416_);
lean_dec_ref_known(v___x_7415_, 1);
v___x_7417_ = ((size_t)1ULL);
v___x_7418_ = lean_usize_add(v_i_7408_, v___x_7417_);
v_i_7408_ = v___x_7418_;
v_b_7410_ = v_a_7416_;
goto _start;
}
}
else
{
lean_object* v___x_7420_; 
lean_dec(v_ps_7406_);
v___x_7420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7420_, 0, v_b_7410_);
return v___x_7420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7421_, lean_object* v_as_7422_, lean_object* v_i_7423_, lean_object* v_stop_7424_, lean_object* v_b_7425_){
_start:
{
size_t v_i_boxed_7426_; size_t v_stop_boxed_7427_; lean_object* v_res_7428_; 
v_i_boxed_7426_ = lean_unbox_usize(v_i_7423_);
lean_dec(v_i_7423_);
v_stop_boxed_7427_ = lean_unbox_usize(v_stop_7424_);
lean_dec(v_stop_7424_);
v_res_7428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7421_, v_as_7422_, v_i_boxed_7426_, v_stop_boxed_7427_, v_b_7425_);
lean_dec_ref(v_as_7422_);
return v_res_7428_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7429_, lean_object* v_k_7430_, lean_object* v_t_7431_){
_start:
{
uint8_t v___x_7432_; 
v___x_7432_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7430_, v_t_7431_);
return v___x_7432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7433_, lean_object* v_k_7434_, lean_object* v_t_7435_){
_start:
{
uint8_t v_res_7436_; lean_object* v_r_7437_; 
v_res_7436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7433_, v_k_7434_, v_t_7435_);
lean_dec(v_t_7435_);
lean_dec_ref(v_k_7434_);
v_r_7437_ = lean_box(v_res_7436_);
return v_r_7437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7438_, lean_object* v_k_7439_, lean_object* v_v_7440_, lean_object* v_t_7441_, lean_object* v_hl_7442_){
_start:
{
lean_object* v___x_7443_; 
v___x_7443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7439_, v_v_7440_, v_t_7441_);
return v___x_7443_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7445_, lean_object* v_a_7446_){
_start:
{
if (lean_obj_tag(v_a_7445_) == 0)
{
lean_object* v___x_7447_; 
v___x_7447_ = l_List_reverse___redArg(v_a_7446_);
return v___x_7447_;
}
else
{
lean_object* v_head_7448_; lean_object* v_tail_7449_; lean_object* v___x_7451_; uint8_t v_isShared_7452_; uint8_t v_isSharedCheck_7459_; 
v_head_7448_ = lean_ctor_get(v_a_7445_, 0);
v_tail_7449_ = lean_ctor_get(v_a_7445_, 1);
v_isSharedCheck_7459_ = !lean_is_exclusive(v_a_7445_);
if (v_isSharedCheck_7459_ == 0)
{
v___x_7451_ = v_a_7445_;
v_isShared_7452_ = v_isSharedCheck_7459_;
goto v_resetjp_7450_;
}
else
{
lean_inc(v_tail_7449_);
lean_inc(v_head_7448_);
lean_dec(v_a_7445_);
v___x_7451_ = lean_box(0);
v_isShared_7452_ = v_isSharedCheck_7459_;
goto v_resetjp_7450_;
}
v_resetjp_7450_:
{
lean_object* v___x_7453_; lean_object* v___x_7454_; lean_object* v___x_7456_; 
v___x_7453_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7454_ = lean_string_append(v___x_7453_, v_head_7448_);
lean_dec(v_head_7448_);
if (v_isShared_7452_ == 0)
{
lean_ctor_set(v___x_7451_, 1, v_a_7446_);
lean_ctor_set(v___x_7451_, 0, v___x_7454_);
v___x_7456_ = v___x_7451_;
goto v_reusejp_7455_;
}
else
{
lean_object* v_reuseFailAlloc_7458_; 
v_reuseFailAlloc_7458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7458_, 0, v___x_7454_);
lean_ctor_set(v_reuseFailAlloc_7458_, 1, v_a_7446_);
v___x_7456_ = v_reuseFailAlloc_7458_;
goto v_reusejp_7455_;
}
v_reusejp_7455_:
{
v_a_7445_ = v_tail_7449_;
v_a_7446_ = v___x_7456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7460_){
_start:
{
lean_object* v___x_7461_; lean_object* v___x_7462_; lean_object* v___x_7463_; lean_object* v___x_7464_; 
v___x_7461_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7462_ = lean_box(0);
v___x_7463_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7460_, v___x_7462_);
v___x_7464_ = l_String_intercalate(v___x_7461_, v___x_7463_);
return v___x_7464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object* v_as_7465_, size_t v_i_7466_, size_t v_stop_7467_, lean_object* v_b_7468_){
_start:
{
uint8_t v___x_7469_; 
v___x_7469_ = lean_usize_dec_eq(v_i_7466_, v_stop_7467_);
if (v___x_7469_ == 0)
{
lean_object* v_fst_7470_; lean_object* v_snd_7471_; lean_object* v___x_7472_; lean_object* v___x_7473_; lean_object* v___x_7474_; 
v_fst_7470_ = lean_ctor_get(v_b_7468_, 0);
lean_inc(v_fst_7470_);
v_snd_7471_ = lean_ctor_get(v_b_7468_, 1);
lean_inc(v_snd_7471_);
lean_dec_ref(v_b_7468_);
v___x_7472_ = lean_array_uget_borrowed(v_as_7465_, v_i_7466_);
v___x_7473_ = lean_box(0);
lean_inc(v___x_7472_);
v___x_7474_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7472_, v___x_7473_, v_fst_7470_, v_snd_7471_);
if (lean_obj_tag(v___x_7474_) == 0)
{
return v___x_7474_;
}
else
{
lean_object* v_a_7475_; size_t v___x_7476_; size_t v___x_7477_; 
v_a_7475_ = lean_ctor_get(v___x_7474_, 0);
lean_inc(v_a_7475_);
lean_dec_ref_known(v___x_7474_, 1);
v___x_7476_ = ((size_t)1ULL);
v___x_7477_ = lean_usize_add(v_i_7466_, v___x_7476_);
v_i_7466_ = v___x_7477_;
v_b_7468_ = v_a_7475_;
goto _start;
}
}
else
{
lean_object* v___x_7479_; 
v___x_7479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7479_, 0, v_b_7468_);
return v___x_7479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7480_, lean_object* v_i_7481_, lean_object* v_stop_7482_, lean_object* v_b_7483_){
_start:
{
size_t v_i_boxed_7484_; size_t v_stop_boxed_7485_; lean_object* v_res_7486_; 
v_i_boxed_7484_ = lean_unbox_usize(v_i_7481_);
lean_dec(v_i_7481_);
v_stop_boxed_7485_ = lean_unbox_usize(v_stop_7482_);
lean_dec(v_stop_7482_);
v_res_7486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_as_7480_, v_i_boxed_7484_, v_stop_boxed_7485_, v_b_7483_);
lean_dec_ref(v_as_7480_);
return v_res_7486_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object* v_libs_7493_, lean_object* v_a_7494_){
_start:
{
lean_object* v_snd_7497_; lean_object* v___y_7500_; lean_object* v___x_7524_; lean_object* v___x_7525_; lean_object* v___x_7526_; uint8_t v___x_7527_; 
v___x_7524_ = lean_unsigned_to_nat(0u);
v___x_7525_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7526_ = lean_array_get_size(v_libs_7493_);
v___x_7527_ = lean_nat_dec_lt(v___x_7524_, v___x_7526_);
if (v___x_7527_ == 0)
{
v_snd_7497_ = v___x_7525_;
goto v___jp_7496_;
}
else
{
lean_object* v___x_7528_; uint8_t v___x_7529_; 
v___x_7528_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__2));
v___x_7529_ = lean_nat_dec_le(v___x_7526_, v___x_7526_);
if (v___x_7529_ == 0)
{
if (v___x_7527_ == 0)
{
v_snd_7497_ = v___x_7525_;
goto v___jp_7496_;
}
else
{
size_t v___x_7530_; size_t v___x_7531_; lean_object* v___x_7532_; 
v___x_7530_ = ((size_t)0ULL);
v___x_7531_ = lean_usize_of_nat(v___x_7526_);
v___x_7532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7493_, v___x_7530_, v___x_7531_, v___x_7528_);
v___y_7500_ = v___x_7532_;
goto v___jp_7499_;
}
}
else
{
size_t v___x_7533_; size_t v___x_7534_; lean_object* v___x_7535_; 
v___x_7533_ = ((size_t)0ULL);
v___x_7534_ = lean_usize_of_nat(v___x_7526_);
v___x_7535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7493_, v___x_7533_, v___x_7534_, v___x_7528_);
v___y_7500_ = v___x_7535_;
goto v___jp_7499_;
}
}
v___jp_7496_:
{
lean_object* v___x_7498_; 
v___x_7498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7498_, 0, v_snd_7497_);
lean_ctor_set(v___x_7498_, 1, v_a_7494_);
return v___x_7498_;
}
v___jp_7499_:
{
if (lean_obj_tag(v___y_7500_) == 0)
{
lean_object* v_a_7501_; lean_object* v_log_7502_; uint8_t v_action_7503_; uint8_t v_wantsRebuild_7504_; lean_object* v_trace_7505_; lean_object* v_buildTime_7506_; lean_object* v___x_7508_; uint8_t v_isShared_7509_; uint8_t v_isSharedCheck_7521_; 
v_a_7501_ = lean_ctor_get(v___y_7500_, 0);
lean_inc(v_a_7501_);
lean_dec_ref_known(v___y_7500_, 1);
v_log_7502_ = lean_ctor_get(v_a_7494_, 0);
v_action_7503_ = lean_ctor_get_uint8(v_a_7494_, sizeof(void*)*3);
v_wantsRebuild_7504_ = lean_ctor_get_uint8(v_a_7494_, sizeof(void*)*3 + 1);
v_trace_7505_ = lean_ctor_get(v_a_7494_, 1);
v_buildTime_7506_ = lean_ctor_get(v_a_7494_, 2);
v_isSharedCheck_7521_ = !lean_is_exclusive(v_a_7494_);
if (v_isSharedCheck_7521_ == 0)
{
v___x_7508_ = v_a_7494_;
v_isShared_7509_ = v_isSharedCheck_7521_;
goto v_resetjp_7507_;
}
else
{
lean_inc(v_buildTime_7506_);
lean_inc(v_trace_7505_);
lean_inc(v_log_7502_);
lean_dec(v_a_7494_);
v___x_7508_ = lean_box(0);
v_isShared_7509_ = v_isSharedCheck_7521_;
goto v_resetjp_7507_;
}
v_resetjp_7507_:
{
lean_object* v___x_7510_; lean_object* v___x_7511_; lean_object* v___x_7512_; uint8_t v___x_7513_; lean_object* v___x_7514_; lean_object* v___x_7515_; lean_object* v___x_7516_; lean_object* v___x_7518_; 
v___x_7510_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__0));
v___x_7511_ = l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(v_a_7501_);
v___x_7512_ = lean_string_append(v___x_7510_, v___x_7511_);
lean_dec_ref(v___x_7511_);
v___x_7513_ = 3;
v___x_7514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7514_, 0, v___x_7512_);
lean_ctor_set_uint8(v___x_7514_, sizeof(void*)*1, v___x_7513_);
v___x_7515_ = lean_array_get_size(v_log_7502_);
v___x_7516_ = lean_array_push(v_log_7502_, v___x_7514_);
if (v_isShared_7509_ == 0)
{
lean_ctor_set(v___x_7508_, 0, v___x_7516_);
v___x_7518_ = v___x_7508_;
goto v_reusejp_7517_;
}
else
{
lean_object* v_reuseFailAlloc_7520_; 
v_reuseFailAlloc_7520_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7520_, 0, v___x_7516_);
lean_ctor_set(v_reuseFailAlloc_7520_, 1, v_trace_7505_);
lean_ctor_set(v_reuseFailAlloc_7520_, 2, v_buildTime_7506_);
lean_ctor_set_uint8(v_reuseFailAlloc_7520_, sizeof(void*)*3, v_action_7503_);
lean_ctor_set_uint8(v_reuseFailAlloc_7520_, sizeof(void*)*3 + 1, v_wantsRebuild_7504_);
v___x_7518_ = v_reuseFailAlloc_7520_;
goto v_reusejp_7517_;
}
v_reusejp_7517_:
{
lean_object* v___x_7519_; 
v___x_7519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7519_, 0, v___x_7515_);
lean_ctor_set(v___x_7519_, 1, v___x_7518_);
return v___x_7519_;
}
}
}
else
{
lean_object* v_a_7522_; lean_object* v_snd_7523_; 
v_a_7522_ = lean_ctor_get(v___y_7500_, 0);
lean_inc(v_a_7522_);
lean_dec_ref_known(v___y_7500_, 1);
v_snd_7523_ = lean_ctor_get(v_a_7522_, 1);
lean_inc(v_snd_7523_);
lean_dec(v_a_7522_);
v_snd_7497_ = v_snd_7523_;
goto v___jp_7496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7536_, lean_object* v_a_7537_, lean_object* v_a_7538_){
_start:
{
lean_object* v_res_7539_; 
v_res_7539_ = l_Lake_mkLinkOrder___redArg(v_libs_7536_, v_a_7537_);
lean_dec_ref(v_libs_7536_);
return v_res_7539_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object* v_libs_7540_, lean_object* v_a_7541_, lean_object* v_a_7542_, lean_object* v_a_7543_, lean_object* v_a_7544_, lean_object* v_a_7545_, lean_object* v_a_7546_){
_start:
{
lean_object* v___x_7548_; 
v___x_7548_ = l_Lake_mkLinkOrder___redArg(v_libs_7540_, v_a_7546_);
return v___x_7548_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object* v_libs_7549_, lean_object* v_a_7550_, lean_object* v_a_7551_, lean_object* v_a_7552_, lean_object* v_a_7553_, lean_object* v_a_7554_, lean_object* v_a_7555_, lean_object* v_a_7556_){
_start:
{
lean_object* v_res_7557_; 
v_res_7557_ = l_Lake_mkLinkOrder(v_libs_7549_, v_a_7550_, v_a_7551_, v_a_7552_, v_a_7553_, v_a_7554_, v_a_7555_);
lean_dec_ref(v_a_7554_);
lean_dec(v_a_7553_);
lean_dec(v_a_7552_);
lean_dec(v_a_7551_);
lean_dec_ref(v_a_7550_);
lean_dec_ref(v_libs_7549_);
return v_res_7557_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object* v_objs_7558_, lean_object* v_libs_7559_, uint8_t v_linkDeps_7560_, lean_object* v_a_7561_){
_start:
{
lean_object* v_libs_7564_; lean_object* v___y_7565_; 
if (v_linkDeps_7560_ == 0)
{
lean_object* v___x_7568_; 
v___x_7568_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7564_ = v___x_7568_;
v___y_7565_ = v_a_7561_;
goto v___jp_7563_;
}
else
{
lean_object* v___x_7569_; 
v___x_7569_ = l_Lake_mkLinkOrder___redArg(v_libs_7559_, v_a_7561_);
if (lean_obj_tag(v___x_7569_) == 0)
{
lean_object* v_a_7570_; lean_object* v_a_7571_; 
v_a_7570_ = lean_ctor_get(v___x_7569_, 0);
lean_inc(v_a_7570_);
v_a_7571_ = lean_ctor_get(v___x_7569_, 1);
lean_inc(v_a_7571_);
lean_dec_ref_known(v___x_7569_, 2);
v_libs_7564_ = v_a_7570_;
v___y_7565_ = v_a_7571_;
goto v___jp_7563_;
}
else
{
lean_object* v_a_7572_; lean_object* v_a_7573_; lean_object* v___x_7575_; uint8_t v_isShared_7576_; uint8_t v_isSharedCheck_7580_; 
v_a_7572_ = lean_ctor_get(v___x_7569_, 0);
v_a_7573_ = lean_ctor_get(v___x_7569_, 1);
v_isSharedCheck_7580_ = !lean_is_exclusive(v___x_7569_);
if (v_isSharedCheck_7580_ == 0)
{
v___x_7575_ = v___x_7569_;
v_isShared_7576_ = v_isSharedCheck_7580_;
goto v_resetjp_7574_;
}
else
{
lean_inc(v_a_7573_);
lean_inc(v_a_7572_);
lean_dec(v___x_7569_);
v___x_7575_ = lean_box(0);
v_isShared_7576_ = v_isSharedCheck_7580_;
goto v_resetjp_7574_;
}
v_resetjp_7574_:
{
lean_object* v___x_7578_; 
if (v_isShared_7576_ == 0)
{
v___x_7578_ = v___x_7575_;
goto v_reusejp_7577_;
}
else
{
lean_object* v_reuseFailAlloc_7579_; 
v_reuseFailAlloc_7579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7579_, 0, v_a_7572_);
lean_ctor_set(v_reuseFailAlloc_7579_, 1, v_a_7573_);
v___x_7578_ = v_reuseFailAlloc_7579_;
goto v_reusejp_7577_;
}
v_reusejp_7577_:
{
return v___x_7578_;
}
}
}
}
v___jp_7563_:
{
lean_object* v___x_7566_; lean_object* v___x_7567_; 
v___x_7566_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7558_, v_libs_7564_);
lean_dec_ref(v_libs_7564_);
v___x_7567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7567_, 0, v___x_7566_);
lean_ctor_set(v___x_7567_, 1, v___y_7565_);
return v___x_7567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object* v_objs_7581_, lean_object* v_libs_7582_, lean_object* v_linkDeps_7583_, lean_object* v_a_7584_, lean_object* v_a_7585_){
_start:
{
uint8_t v_linkDeps_boxed_7586_; lean_object* v_res_7587_; 
v_linkDeps_boxed_7586_ = lean_unbox(v_linkDeps_7583_);
v_res_7587_ = l_Lake_mkLinkArgs___redArg(v_objs_7581_, v_libs_7582_, v_linkDeps_boxed_7586_, v_a_7584_);
lean_dec_ref(v_libs_7582_);
lean_dec_ref(v_objs_7581_);
return v_res_7587_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object* v_objs_7588_, lean_object* v_libs_7589_, uint8_t v_linkDeps_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_){
_start:
{
lean_object* v_libs_7599_; lean_object* v___y_7600_; 
if (v_linkDeps_7590_ == 0)
{
lean_object* v___x_7603_; 
v___x_7603_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7599_ = v___x_7603_;
v___y_7600_ = v_a_7596_;
goto v___jp_7598_;
}
else
{
lean_object* v___x_7604_; 
v___x_7604_ = l_Lake_mkLinkOrder___redArg(v_libs_7589_, v_a_7596_);
if (lean_obj_tag(v___x_7604_) == 0)
{
lean_object* v_a_7605_; lean_object* v_a_7606_; 
v_a_7605_ = lean_ctor_get(v___x_7604_, 0);
lean_inc(v_a_7605_);
v_a_7606_ = lean_ctor_get(v___x_7604_, 1);
lean_inc(v_a_7606_);
lean_dec_ref_known(v___x_7604_, 2);
v_libs_7599_ = v_a_7605_;
v___y_7600_ = v_a_7606_;
goto v___jp_7598_;
}
else
{
lean_object* v_a_7607_; lean_object* v_a_7608_; lean_object* v___x_7610_; uint8_t v_isShared_7611_; uint8_t v_isSharedCheck_7615_; 
v_a_7607_ = lean_ctor_get(v___x_7604_, 0);
v_a_7608_ = lean_ctor_get(v___x_7604_, 1);
v_isSharedCheck_7615_ = !lean_is_exclusive(v___x_7604_);
if (v_isSharedCheck_7615_ == 0)
{
v___x_7610_ = v___x_7604_;
v_isShared_7611_ = v_isSharedCheck_7615_;
goto v_resetjp_7609_;
}
else
{
lean_inc(v_a_7608_);
lean_inc(v_a_7607_);
lean_dec(v___x_7604_);
v___x_7610_ = lean_box(0);
v_isShared_7611_ = v_isSharedCheck_7615_;
goto v_resetjp_7609_;
}
v_resetjp_7609_:
{
lean_object* v___x_7613_; 
if (v_isShared_7611_ == 0)
{
v___x_7613_ = v___x_7610_;
goto v_reusejp_7612_;
}
else
{
lean_object* v_reuseFailAlloc_7614_; 
v_reuseFailAlloc_7614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7614_, 0, v_a_7607_);
lean_ctor_set(v_reuseFailAlloc_7614_, 1, v_a_7608_);
v___x_7613_ = v_reuseFailAlloc_7614_;
goto v_reusejp_7612_;
}
v_reusejp_7612_:
{
return v___x_7613_;
}
}
}
}
v___jp_7598_:
{
lean_object* v___x_7601_; lean_object* v___x_7602_; 
v___x_7601_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7588_, v_libs_7599_);
lean_dec_ref(v_libs_7599_);
v___x_7602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7602_, 0, v___x_7601_);
lean_ctor_set(v___x_7602_, 1, v___y_7600_);
return v___x_7602_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object* v_objs_7616_, lean_object* v_libs_7617_, lean_object* v_linkDeps_7618_, lean_object* v_a_7619_, lean_object* v_a_7620_, lean_object* v_a_7621_, lean_object* v_a_7622_, lean_object* v_a_7623_, lean_object* v_a_7624_, lean_object* v_a_7625_){
_start:
{
uint8_t v_linkDeps_boxed_7626_; lean_object* v_res_7627_; 
v_linkDeps_boxed_7626_ = lean_unbox(v_linkDeps_7618_);
v_res_7627_ = l_Lake_mkLinkArgs(v_objs_7616_, v_libs_7617_, v_linkDeps_boxed_7626_, v_a_7619_, v_a_7620_, v_a_7621_, v_a_7622_, v_a_7623_, v_a_7624_);
lean_dec_ref(v_a_7623_);
lean_dec(v_a_7622_);
lean_dec(v_a_7621_);
lean_dec(v_a_7620_);
lean_dec_ref(v_a_7619_);
lean_dec_ref(v_libs_7617_);
lean_dec_ref(v_objs_7616_);
return v_res_7627_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0(void){
_start:
{
lean_object* v___x_7628_; lean_object* v___x_7629_; lean_object* v___x_7630_; lean_object* v___x_7631_; 
v___x_7628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7629_ = lean_unsigned_to_nat(2u);
v___x_7630_ = lean_mk_empty_array_with_capacity(v___x_7629_);
v___x_7631_ = lean_array_push(v___x_7630_, v___x_7628_);
return v___x_7631_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object* v_objs_7632_, lean_object* v_libs_7633_, lean_object* v_args_7634_, uint8_t v_linkDeps_7635_, uint8_t v_sharedLean_7636_, lean_object* v_a_7637_, lean_object* v_a_7638_){
_start:
{
lean_object* v_toContext_7640_; lean_object* v_lakeEnv_7641_; lean_object* v_lean_7642_; lean_object* v_libs_7644_; lean_object* v___y_7645_; 
v_toContext_7640_ = lean_ctor_get(v_a_7637_, 1);
v_lakeEnv_7641_ = lean_ctor_get(v_toContext_7640_, 0);
v_lean_7642_ = lean_ctor_get(v_lakeEnv_7641_, 1);
if (v_linkDeps_7635_ == 0)
{
lean_object* v___x_7655_; 
v___x_7655_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7644_ = v___x_7655_;
v___y_7645_ = v_a_7638_;
goto v___jp_7643_;
}
else
{
lean_object* v___x_7656_; 
v___x_7656_ = l_Lake_mkLinkOrder___redArg(v_libs_7633_, v_a_7638_);
if (lean_obj_tag(v___x_7656_) == 0)
{
lean_object* v_a_7657_; lean_object* v_a_7658_; 
v_a_7657_ = lean_ctor_get(v___x_7656_, 0);
lean_inc(v_a_7657_);
v_a_7658_ = lean_ctor_get(v___x_7656_, 1);
lean_inc(v_a_7658_);
lean_dec_ref_known(v___x_7656_, 2);
v_libs_7644_ = v_a_7657_;
v___y_7645_ = v_a_7658_;
goto v___jp_7643_;
}
else
{
lean_object* v_a_7659_; lean_object* v_a_7660_; lean_object* v___x_7662_; uint8_t v_isShared_7663_; uint8_t v_isSharedCheck_7667_; 
v_a_7659_ = lean_ctor_get(v___x_7656_, 0);
v_a_7660_ = lean_ctor_get(v___x_7656_, 1);
v_isSharedCheck_7667_ = !lean_is_exclusive(v___x_7656_);
if (v_isSharedCheck_7667_ == 0)
{
v___x_7662_ = v___x_7656_;
v_isShared_7663_ = v_isSharedCheck_7667_;
goto v_resetjp_7661_;
}
else
{
lean_inc(v_a_7660_);
lean_inc(v_a_7659_);
lean_dec(v___x_7656_);
v___x_7662_ = lean_box(0);
v_isShared_7663_ = v_isSharedCheck_7667_;
goto v_resetjp_7661_;
}
v_resetjp_7661_:
{
lean_object* v___x_7665_; 
if (v_isShared_7663_ == 0)
{
v___x_7665_ = v___x_7662_;
goto v_reusejp_7664_;
}
else
{
lean_object* v_reuseFailAlloc_7666_; 
v_reuseFailAlloc_7666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7666_, 0, v_a_7659_);
lean_ctor_set(v_reuseFailAlloc_7666_, 1, v_a_7660_);
v___x_7665_ = v_reuseFailAlloc_7666_;
goto v_reusejp_7664_;
}
v_reusejp_7664_:
{
return v___x_7665_;
}
}
}
}
v___jp_7643_:
{
lean_object* v_leanLibDir_7646_; lean_object* v___x_7647_; lean_object* v___x_7648_; lean_object* v___x_7649_; lean_object* v___x_7650_; lean_object* v___x_7651_; lean_object* v___x_7652_; lean_object* v___x_7653_; lean_object* v___x_7654_; 
v_leanLibDir_7646_ = lean_ctor_get(v_lean_7642_, 3);
v___x_7647_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7632_, v_libs_7644_);
lean_dec_ref(v_libs_7644_);
v___x_7648_ = l_Array_append___redArg(v___x_7647_, v_args_7634_);
v___x_7649_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7646_);
v___x_7650_ = lean_array_push(v___x_7649_, v_leanLibDir_7646_);
v___x_7651_ = l_Array_append___redArg(v___x_7648_, v___x_7650_);
lean_dec_ref(v___x_7650_);
v___x_7652_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7636_, v_lean_7642_);
v___x_7653_ = l_Array_append___redArg(v___x_7651_, v___x_7652_);
lean_dec_ref(v___x_7652_);
v___x_7654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7654_, 0, v___x_7653_);
lean_ctor_set(v___x_7654_, 1, v___y_7645_);
return v___x_7654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object* v_objs_7668_, lean_object* v_libs_7669_, lean_object* v_args_7670_, lean_object* v_linkDeps_7671_, lean_object* v_sharedLean_7672_, lean_object* v_a_7673_, lean_object* v_a_7674_, lean_object* v_a_7675_){
_start:
{
uint8_t v_linkDeps_boxed_7676_; uint8_t v_sharedLean_boxed_7677_; lean_object* v_res_7678_; 
v_linkDeps_boxed_7676_ = lean_unbox(v_linkDeps_7671_);
v_sharedLean_boxed_7677_ = lean_unbox(v_sharedLean_7672_);
v_res_7678_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(v_objs_7668_, v_libs_7669_, v_args_7670_, v_linkDeps_boxed_7676_, v_sharedLean_boxed_7677_, v_a_7673_, v_a_7674_);
lean_dec_ref(v_a_7673_);
lean_dec_ref(v_args_7670_);
lean_dec_ref(v_libs_7669_);
lean_dec_ref(v_objs_7668_);
return v_res_7678_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object* v_objs_7679_, lean_object* v_libs_7680_, lean_object* v_args_7681_, uint8_t v_linkDeps_7682_, uint8_t v_sharedLean_7683_, lean_object* v_a_7684_, lean_object* v_a_7685_, lean_object* v_a_7686_, lean_object* v_a_7687_, lean_object* v_a_7688_, lean_object* v_a_7689_){
_start:
{
lean_object* v_toContext_7691_; lean_object* v_lakeEnv_7692_; lean_object* v_lean_7693_; lean_object* v_libs_7695_; lean_object* v___y_7696_; 
v_toContext_7691_ = lean_ctor_get(v_a_7688_, 1);
v_lakeEnv_7692_ = lean_ctor_get(v_toContext_7691_, 0);
v_lean_7693_ = lean_ctor_get(v_lakeEnv_7692_, 1);
if (v_linkDeps_7682_ == 0)
{
lean_object* v___x_7708_; 
v___x_7708_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7695_ = v___x_7708_;
v___y_7696_ = v_a_7689_;
goto v___jp_7694_;
}
else
{
lean_object* v___x_7709_; 
v___x_7709_ = l_Lake_mkLinkOrder___redArg(v_libs_7680_, v_a_7689_);
if (lean_obj_tag(v___x_7709_) == 0)
{
lean_object* v_a_7710_; lean_object* v_a_7711_; 
v_a_7710_ = lean_ctor_get(v___x_7709_, 0);
lean_inc(v_a_7710_);
v_a_7711_ = lean_ctor_get(v___x_7709_, 1);
lean_inc(v_a_7711_);
lean_dec_ref_known(v___x_7709_, 2);
v_libs_7695_ = v_a_7710_;
v___y_7696_ = v_a_7711_;
goto v___jp_7694_;
}
else
{
lean_object* v_a_7712_; lean_object* v_a_7713_; lean_object* v___x_7715_; uint8_t v_isShared_7716_; uint8_t v_isSharedCheck_7720_; 
v_a_7712_ = lean_ctor_get(v___x_7709_, 0);
v_a_7713_ = lean_ctor_get(v___x_7709_, 1);
v_isSharedCheck_7720_ = !lean_is_exclusive(v___x_7709_);
if (v_isSharedCheck_7720_ == 0)
{
v___x_7715_ = v___x_7709_;
v_isShared_7716_ = v_isSharedCheck_7720_;
goto v_resetjp_7714_;
}
else
{
lean_inc(v_a_7713_);
lean_inc(v_a_7712_);
lean_dec(v___x_7709_);
v___x_7715_ = lean_box(0);
v_isShared_7716_ = v_isSharedCheck_7720_;
goto v_resetjp_7714_;
}
v_resetjp_7714_:
{
lean_object* v___x_7718_; 
if (v_isShared_7716_ == 0)
{
v___x_7718_ = v___x_7715_;
goto v_reusejp_7717_;
}
else
{
lean_object* v_reuseFailAlloc_7719_; 
v_reuseFailAlloc_7719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7719_, 0, v_a_7712_);
lean_ctor_set(v_reuseFailAlloc_7719_, 1, v_a_7713_);
v___x_7718_ = v_reuseFailAlloc_7719_;
goto v_reusejp_7717_;
}
v_reusejp_7717_:
{
return v___x_7718_;
}
}
}
}
v___jp_7694_:
{
lean_object* v_leanLibDir_7697_; lean_object* v___x_7698_; lean_object* v___x_7699_; lean_object* v___x_7700_; lean_object* v___x_7701_; lean_object* v___x_7702_; lean_object* v___x_7703_; lean_object* v___x_7704_; lean_object* v___x_7705_; lean_object* v___x_7706_; lean_object* v___x_7707_; 
v_leanLibDir_7697_ = lean_ctor_get(v_lean_7693_, 3);
v___x_7698_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7679_, v_libs_7695_);
lean_dec_ref(v_libs_7695_);
v___x_7699_ = l_Array_append___redArg(v___x_7698_, v_args_7681_);
v___x_7700_ = lean_unsigned_to_nat(2u);
v___x_7701_ = lean_mk_empty_array_with_capacity(v___x_7700_);
lean_dec_ref(v___x_7701_);
v___x_7702_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7697_);
v___x_7703_ = lean_array_push(v___x_7702_, v_leanLibDir_7697_);
v___x_7704_ = l_Array_append___redArg(v___x_7699_, v___x_7703_);
lean_dec_ref(v___x_7703_);
v___x_7705_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7683_, v_lean_7693_);
v___x_7706_ = l_Array_append___redArg(v___x_7704_, v___x_7705_);
lean_dec_ref(v___x_7705_);
v___x_7707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7707_, 0, v___x_7706_);
lean_ctor_set(v___x_7707_, 1, v___y_7696_);
return v___x_7707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object* v_objs_7721_, lean_object* v_libs_7722_, lean_object* v_args_7723_, lean_object* v_linkDeps_7724_, lean_object* v_sharedLean_7725_, lean_object* v_a_7726_, lean_object* v_a_7727_, lean_object* v_a_7728_, lean_object* v_a_7729_, lean_object* v_a_7730_, lean_object* v_a_7731_, lean_object* v_a_7732_){
_start:
{
uint8_t v_linkDeps_boxed_7733_; uint8_t v_sharedLean_boxed_7734_; lean_object* v_res_7735_; 
v_linkDeps_boxed_7733_ = lean_unbox(v_linkDeps_7724_);
v_sharedLean_boxed_7734_ = lean_unbox(v_sharedLean_7725_);
v_res_7735_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(v_objs_7721_, v_libs_7722_, v_args_7723_, v_linkDeps_boxed_7733_, v_sharedLean_boxed_7734_, v_a_7726_, v_a_7727_, v_a_7728_, v_a_7729_, v_a_7730_, v_a_7731_);
lean_dec_ref(v_a_7730_);
lean_dec(v_a_7729_);
lean_dec(v_a_7728_);
lean_dec(v_a_7727_);
lean_dec_ref(v_a_7726_);
lean_dec_ref(v_args_7723_);
lean_dec_ref(v_libs_7722_);
lean_dec_ref(v_objs_7721_);
return v_res_7735_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object* v_linkObjs_7736_, lean_object* v_args_7737_, lean_object* v_libFile_7738_, lean_object* v_linker_7739_, lean_object* v___y_7740_, uint8_t v_linkDeps_7741_, lean_object* v_linkLibs_7742_, lean_object* v___y_7743_, lean_object* v___y_7744_, lean_object* v___y_7745_, lean_object* v___y_7746_, lean_object* v___y_7747_, lean_object* v___y_7748_){
_start:
{
lean_object* v_libs_7751_; lean_object* v___y_7752_; 
if (v_linkDeps_7741_ == 0)
{
lean_object* v___x_7789_; 
v___x_7789_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7751_ = v___x_7789_;
v___y_7752_ = v___y_7748_;
goto v___jp_7750_;
}
else
{
lean_object* v___x_7790_; 
v___x_7790_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_7742_, v___y_7748_);
if (lean_obj_tag(v___x_7790_) == 0)
{
lean_object* v_a_7791_; lean_object* v_a_7792_; 
v_a_7791_ = lean_ctor_get(v___x_7790_, 0);
lean_inc(v_a_7791_);
v_a_7792_ = lean_ctor_get(v___x_7790_, 1);
lean_inc(v_a_7792_);
lean_dec_ref_known(v___x_7790_, 2);
v_libs_7751_ = v_a_7791_;
v___y_7752_ = v_a_7792_;
goto v___jp_7750_;
}
else
{
lean_object* v_a_7793_; lean_object* v_a_7794_; lean_object* v___x_7796_; uint8_t v_isShared_7797_; uint8_t v_isSharedCheck_7801_; 
lean_dec(v___y_7740_);
lean_dec_ref(v_linker_7739_);
lean_dec_ref(v_libFile_7738_);
v_a_7793_ = lean_ctor_get(v___x_7790_, 0);
v_a_7794_ = lean_ctor_get(v___x_7790_, 1);
v_isSharedCheck_7801_ = !lean_is_exclusive(v___x_7790_);
if (v_isSharedCheck_7801_ == 0)
{
v___x_7796_ = v___x_7790_;
v_isShared_7797_ = v_isSharedCheck_7801_;
goto v_resetjp_7795_;
}
else
{
lean_inc(v_a_7794_);
lean_inc(v_a_7793_);
lean_dec(v___x_7790_);
v___x_7796_ = lean_box(0);
v_isShared_7797_ = v_isSharedCheck_7801_;
goto v_resetjp_7795_;
}
v_resetjp_7795_:
{
lean_object* v___x_7799_; 
if (v_isShared_7797_ == 0)
{
v___x_7799_ = v___x_7796_;
goto v_reusejp_7798_;
}
else
{
lean_object* v_reuseFailAlloc_7800_; 
v_reuseFailAlloc_7800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7800_, 0, v_a_7793_);
lean_ctor_set(v_reuseFailAlloc_7800_, 1, v_a_7794_);
v___x_7799_ = v_reuseFailAlloc_7800_;
goto v_reusejp_7798_;
}
v_reusejp_7798_:
{
return v___x_7799_;
}
}
}
}
v___jp_7750_:
{
lean_object* v_log_7753_; uint8_t v_action_7754_; uint8_t v_wantsRebuild_7755_; lean_object* v_trace_7756_; lean_object* v_buildTime_7757_; lean_object* v___x_7759_; uint8_t v_isShared_7760_; uint8_t v_isSharedCheck_7788_; 
v_log_7753_ = lean_ctor_get(v___y_7752_, 0);
v_action_7754_ = lean_ctor_get_uint8(v___y_7752_, sizeof(void*)*3);
v_wantsRebuild_7755_ = lean_ctor_get_uint8(v___y_7752_, sizeof(void*)*3 + 1);
v_trace_7756_ = lean_ctor_get(v___y_7752_, 1);
v_buildTime_7757_ = lean_ctor_get(v___y_7752_, 2);
v_isSharedCheck_7788_ = !lean_is_exclusive(v___y_7752_);
if (v_isSharedCheck_7788_ == 0)
{
v___x_7759_ = v___y_7752_;
v_isShared_7760_ = v_isSharedCheck_7788_;
goto v_resetjp_7758_;
}
else
{
lean_inc(v_buildTime_7757_);
lean_inc(v_trace_7756_);
lean_inc(v_log_7753_);
lean_dec(v___y_7752_);
v___x_7759_ = lean_box(0);
v_isShared_7760_ = v_isSharedCheck_7788_;
goto v_resetjp_7758_;
}
v_resetjp_7758_:
{
lean_object* v___x_7761_; lean_object* v___x_7762_; lean_object* v___x_7763_; 
v___x_7761_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_7736_, v_libs_7751_);
lean_dec_ref(v_libs_7751_);
v___x_7762_ = l_Array_append___redArg(v___x_7761_, v_args_7737_);
v___x_7763_ = l_Lake_compileSharedLib(v_libFile_7738_, v___x_7762_, v_linker_7739_, v___y_7740_, v_log_7753_);
lean_dec_ref(v___x_7762_);
if (lean_obj_tag(v___x_7763_) == 0)
{
lean_object* v_a_7764_; lean_object* v_a_7765_; lean_object* v___x_7767_; uint8_t v_isShared_7768_; uint8_t v_isSharedCheck_7775_; 
v_a_7764_ = lean_ctor_get(v___x_7763_, 0);
v_a_7765_ = lean_ctor_get(v___x_7763_, 1);
v_isSharedCheck_7775_ = !lean_is_exclusive(v___x_7763_);
if (v_isSharedCheck_7775_ == 0)
{
v___x_7767_ = v___x_7763_;
v_isShared_7768_ = v_isSharedCheck_7775_;
goto v_resetjp_7766_;
}
else
{
lean_inc(v_a_7765_);
lean_inc(v_a_7764_);
lean_dec(v___x_7763_);
v___x_7767_ = lean_box(0);
v_isShared_7768_ = v_isSharedCheck_7775_;
goto v_resetjp_7766_;
}
v_resetjp_7766_:
{
lean_object* v___x_7770_; 
if (v_isShared_7760_ == 0)
{
lean_ctor_set(v___x_7759_, 0, v_a_7765_);
v___x_7770_ = v___x_7759_;
goto v_reusejp_7769_;
}
else
{
lean_object* v_reuseFailAlloc_7774_; 
v_reuseFailAlloc_7774_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7774_, 0, v_a_7765_);
lean_ctor_set(v_reuseFailAlloc_7774_, 1, v_trace_7756_);
lean_ctor_set(v_reuseFailAlloc_7774_, 2, v_buildTime_7757_);
lean_ctor_set_uint8(v_reuseFailAlloc_7774_, sizeof(void*)*3, v_action_7754_);
lean_ctor_set_uint8(v_reuseFailAlloc_7774_, sizeof(void*)*3 + 1, v_wantsRebuild_7755_);
v___x_7770_ = v_reuseFailAlloc_7774_;
goto v_reusejp_7769_;
}
v_reusejp_7769_:
{
lean_object* v___x_7772_; 
if (v_isShared_7768_ == 0)
{
lean_ctor_set(v___x_7767_, 1, v___x_7770_);
v___x_7772_ = v___x_7767_;
goto v_reusejp_7771_;
}
else
{
lean_object* v_reuseFailAlloc_7773_; 
v_reuseFailAlloc_7773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7773_, 0, v_a_7764_);
lean_ctor_set(v_reuseFailAlloc_7773_, 1, v___x_7770_);
v___x_7772_ = v_reuseFailAlloc_7773_;
goto v_reusejp_7771_;
}
v_reusejp_7771_:
{
return v___x_7772_;
}
}
}
}
else
{
lean_object* v_a_7776_; lean_object* v_a_7777_; lean_object* v___x_7779_; uint8_t v_isShared_7780_; uint8_t v_isSharedCheck_7787_; 
v_a_7776_ = lean_ctor_get(v___x_7763_, 0);
v_a_7777_ = lean_ctor_get(v___x_7763_, 1);
v_isSharedCheck_7787_ = !lean_is_exclusive(v___x_7763_);
if (v_isSharedCheck_7787_ == 0)
{
v___x_7779_ = v___x_7763_;
v_isShared_7780_ = v_isSharedCheck_7787_;
goto v_resetjp_7778_;
}
else
{
lean_inc(v_a_7777_);
lean_inc(v_a_7776_);
lean_dec(v___x_7763_);
v___x_7779_ = lean_box(0);
v_isShared_7780_ = v_isSharedCheck_7787_;
goto v_resetjp_7778_;
}
v_resetjp_7778_:
{
lean_object* v___x_7782_; 
if (v_isShared_7760_ == 0)
{
lean_ctor_set(v___x_7759_, 0, v_a_7777_);
v___x_7782_ = v___x_7759_;
goto v_reusejp_7781_;
}
else
{
lean_object* v_reuseFailAlloc_7786_; 
v_reuseFailAlloc_7786_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7786_, 0, v_a_7777_);
lean_ctor_set(v_reuseFailAlloc_7786_, 1, v_trace_7756_);
lean_ctor_set(v_reuseFailAlloc_7786_, 2, v_buildTime_7757_);
lean_ctor_set_uint8(v_reuseFailAlloc_7786_, sizeof(void*)*3, v_action_7754_);
lean_ctor_set_uint8(v_reuseFailAlloc_7786_, sizeof(void*)*3 + 1, v_wantsRebuild_7755_);
v___x_7782_ = v_reuseFailAlloc_7786_;
goto v_reusejp_7781_;
}
v_reusejp_7781_:
{
lean_object* v___x_7784_; 
if (v_isShared_7780_ == 0)
{
lean_ctor_set(v___x_7779_, 1, v___x_7782_);
v___x_7784_ = v___x_7779_;
goto v_reusejp_7783_;
}
else
{
lean_object* v_reuseFailAlloc_7785_; 
v_reuseFailAlloc_7785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7785_, 0, v_a_7776_);
lean_ctor_set(v_reuseFailAlloc_7785_, 1, v___x_7782_);
v___x_7784_ = v_reuseFailAlloc_7785_;
goto v_reusejp_7783_;
}
v_reusejp_7783_:
{
return v___x_7784_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_7802_, lean_object* v_args_7803_, lean_object* v_libFile_7804_, lean_object* v_linker_7805_, lean_object* v___y_7806_, lean_object* v_linkDeps_7807_, lean_object* v_linkLibs_7808_, lean_object* v___y_7809_, lean_object* v___y_7810_, lean_object* v___y_7811_, lean_object* v___y_7812_, lean_object* v___y_7813_, lean_object* v___y_7814_, lean_object* v___y_7815_){
_start:
{
uint8_t v_linkDeps_boxed_7816_; lean_object* v_res_7817_; 
v_linkDeps_boxed_7816_ = lean_unbox(v_linkDeps_7807_);
v_res_7817_ = l_Lake_buildSharedLibSync___lam__0(v_linkObjs_7802_, v_args_7803_, v_libFile_7804_, v_linker_7805_, v___y_7806_, v_linkDeps_boxed_7816_, v_linkLibs_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_);
lean_dec_ref(v___y_7813_);
lean_dec(v___y_7812_);
lean_dec(v___y_7811_);
lean_dec(v___y_7810_);
lean_dec_ref(v___y_7809_);
lean_dec_ref(v_linkLibs_7808_);
lean_dec_ref(v_args_7803_);
lean_dec_ref(v_linkObjs_7802_);
return v_res_7817_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object* v_libName_7819_, lean_object* v_libFile_7820_, lean_object* v_linkObjs_7821_, lean_object* v_linkLibs_7822_, lean_object* v_args_7823_, lean_object* v_linker_7824_, uint8_t v_plugin_7825_, uint8_t v_linkDeps_7826_, lean_object* v_macosxDeploymentTarget_x3f_7827_, lean_object* v_a_7828_, lean_object* v_a_7829_, lean_object* v_a_7830_, lean_object* v_a_7831_, lean_object* v_a_7832_, lean_object* v_a_7833_){
_start:
{
lean_object* v___y_7836_; lean_object* v___y_7837_; lean_object* v___y_7838_; lean_object* v___y_7839_; lean_object* v___y_7840_; lean_object* v___y_7841_; lean_object* v___y_7842_; lean_object* v_log_7868_; uint8_t v_action_7869_; uint8_t v_wantsRebuild_7870_; lean_object* v_trace_7871_; lean_object* v_buildTime_7872_; lean_object* v___x_7874_; uint8_t v_isShared_7875_; uint8_t v_isSharedCheck_7902_; 
v_log_7868_ = lean_ctor_get(v_a_7833_, 0);
v_action_7869_ = lean_ctor_get_uint8(v_a_7833_, sizeof(void*)*3);
v_wantsRebuild_7870_ = lean_ctor_get_uint8(v_a_7833_, sizeof(void*)*3 + 1);
v_trace_7871_ = lean_ctor_get(v_a_7833_, 1);
v_buildTime_7872_ = lean_ctor_get(v_a_7833_, 2);
v_isSharedCheck_7902_ = !lean_is_exclusive(v_a_7833_);
if (v_isSharedCheck_7902_ == 0)
{
v___x_7874_ = v_a_7833_;
v_isShared_7875_ = v_isSharedCheck_7902_;
goto v_resetjp_7873_;
}
else
{
lean_inc(v_buildTime_7872_);
lean_inc(v_trace_7871_);
lean_inc(v_log_7868_);
lean_dec(v_a_7833_);
v___x_7874_ = lean_box(0);
v_isShared_7875_ = v_isSharedCheck_7902_;
goto v_resetjp_7873_;
}
v___jp_7835_:
{
uint8_t v___x_7843_; lean_object* v___x_7844_; uint8_t v___x_7845_; lean_object* v___x_7846_; 
v___x_7843_ = 0;
v___x_7844_ = l_Lake_sharedLibExt;
v___x_7845_ = 1;
v___x_7846_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7820_, v___y_7836_, v___x_7843_, v___x_7844_, v___x_7845_, v___x_7843_, v___x_7843_, v___y_7837_, v___y_7838_, v___y_7839_, v___y_7840_, v___y_7841_, v___y_7842_);
if (lean_obj_tag(v___x_7846_) == 0)
{
lean_object* v_a_7847_; lean_object* v_a_7848_; lean_object* v___x_7850_; uint8_t v_isShared_7851_; uint8_t v_isSharedCheck_7858_; 
v_a_7847_ = lean_ctor_get(v___x_7846_, 0);
v_a_7848_ = lean_ctor_get(v___x_7846_, 1);
v_isSharedCheck_7858_ = !lean_is_exclusive(v___x_7846_);
if (v_isSharedCheck_7858_ == 0)
{
v___x_7850_ = v___x_7846_;
v_isShared_7851_ = v_isSharedCheck_7858_;
goto v_resetjp_7849_;
}
else
{
lean_inc(v_a_7848_);
lean_inc(v_a_7847_);
lean_dec(v___x_7846_);
v___x_7850_ = lean_box(0);
v_isShared_7851_ = v_isSharedCheck_7858_;
goto v_resetjp_7849_;
}
v_resetjp_7849_:
{
lean_object* v_path_7852_; lean_object* v___x_7853_; lean_object* v___x_7854_; lean_object* v___x_7856_; 
v_path_7852_ = lean_ctor_get(v_a_7847_, 1);
lean_inc_ref(v_path_7852_);
lean_dec(v_a_7847_);
v___x_7853_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7854_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_7854_, 0, v_path_7852_);
lean_ctor_set(v___x_7854_, 1, v_libName_7819_);
lean_ctor_set(v___x_7854_, 2, v_linkLibs_7822_);
lean_ctor_set(v___x_7854_, 3, v___x_7853_);
lean_ctor_set_uint8(v___x_7854_, sizeof(void*)*4, v_plugin_7825_);
if (v_isShared_7851_ == 0)
{
lean_ctor_set(v___x_7850_, 0, v___x_7854_);
v___x_7856_ = v___x_7850_;
goto v_reusejp_7855_;
}
else
{
lean_object* v_reuseFailAlloc_7857_; 
v_reuseFailAlloc_7857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7857_, 0, v___x_7854_);
lean_ctor_set(v_reuseFailAlloc_7857_, 1, v_a_7848_);
v___x_7856_ = v_reuseFailAlloc_7857_;
goto v_reusejp_7855_;
}
v_reusejp_7855_:
{
return v___x_7856_;
}
}
}
else
{
lean_object* v_a_7859_; lean_object* v_a_7860_; lean_object* v___x_7862_; uint8_t v_isShared_7863_; uint8_t v_isSharedCheck_7867_; 
lean_dec_ref(v_linkLibs_7822_);
lean_dec_ref(v_libName_7819_);
v_a_7859_ = lean_ctor_get(v___x_7846_, 0);
v_a_7860_ = lean_ctor_get(v___x_7846_, 1);
v_isSharedCheck_7867_ = !lean_is_exclusive(v___x_7846_);
if (v_isSharedCheck_7867_ == 0)
{
v___x_7862_ = v___x_7846_;
v_isShared_7863_ = v_isSharedCheck_7867_;
goto v_resetjp_7861_;
}
else
{
lean_inc(v_a_7860_);
lean_inc(v_a_7859_);
lean_dec(v___x_7846_);
v___x_7862_ = lean_box(0);
v_isShared_7863_ = v_isSharedCheck_7867_;
goto v_resetjp_7861_;
}
v_resetjp_7861_:
{
lean_object* v___x_7865_; 
if (v_isShared_7863_ == 0)
{
v___x_7865_ = v___x_7862_;
goto v_reusejp_7864_;
}
else
{
lean_object* v_reuseFailAlloc_7866_; 
v_reuseFailAlloc_7866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7866_, 0, v_a_7859_);
lean_ctor_set(v_reuseFailAlloc_7866_, 1, v_a_7860_);
v___x_7865_ = v_reuseFailAlloc_7866_;
goto v_reusejp_7864_;
}
v_reusejp_7864_:
{
return v___x_7865_;
}
}
}
}
v_resetjp_7873_:
{
lean_object* v___x_7876_; lean_object* v___x_7877_; lean_object* v___x_7879_; 
v___x_7876_ = l_Lake_platformTrace;
v___x_7877_ = l_Lake_BuildTrace_mix(v_trace_7871_, v___x_7876_);
lean_inc(v_buildTime_7872_);
lean_inc_ref(v___x_7877_);
lean_inc_ref(v_log_7868_);
if (v_isShared_7875_ == 0)
{
lean_ctor_set(v___x_7874_, 1, v___x_7877_);
v___x_7879_ = v___x_7874_;
goto v_reusejp_7878_;
}
else
{
lean_object* v_reuseFailAlloc_7901_; 
v_reuseFailAlloc_7901_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7901_, 0, v_log_7868_);
lean_ctor_set(v_reuseFailAlloc_7901_, 1, v___x_7877_);
lean_ctor_set(v_reuseFailAlloc_7901_, 2, v_buildTime_7872_);
lean_ctor_set_uint8(v_reuseFailAlloc_7901_, sizeof(void*)*3, v_action_7869_);
lean_ctor_set_uint8(v_reuseFailAlloc_7901_, sizeof(void*)*3 + 1, v_wantsRebuild_7870_);
v___x_7879_ = v_reuseFailAlloc_7901_;
goto v_reusejp_7878_;
}
v_reusejp_7878_:
{
lean_object* v___y_7881_; lean_object* v_val_7882_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7827_) == 0)
{
lean_object* v_toBuildConfig_7895_; lean_object* v_macosxDeploymentTarget_x3f_7896_; lean_object* v___x_7897_; lean_object* v___f_7898_; 
v_toBuildConfig_7895_ = lean_ctor_get(v_a_7832_, 0);
v_macosxDeploymentTarget_x3f_7896_ = lean_ctor_get(v_toBuildConfig_7895_, 3);
v___x_7897_ = lean_box(v_linkDeps_7826_);
lean_inc_ref(v_linkLibs_7822_);
lean_inc(v_macosxDeploymentTarget_x3f_7896_);
lean_inc_ref(v_linker_7824_);
lean_inc_ref(v_libFile_7820_);
lean_inc_ref(v_args_7823_);
lean_inc_ref(v_linkObjs_7821_);
v___f_7898_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7898_, 0, v_linkObjs_7821_);
lean_closure_set(v___f_7898_, 1, v_args_7823_);
lean_closure_set(v___f_7898_, 2, v_libFile_7820_);
lean_closure_set(v___f_7898_, 3, v_linker_7824_);
lean_closure_set(v___f_7898_, 4, v_macosxDeploymentTarget_x3f_7896_);
lean_closure_set(v___f_7898_, 5, v___x_7897_);
lean_closure_set(v___f_7898_, 6, v_linkLibs_7822_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7896_) == 1)
{
lean_object* v_val_7899_; 
lean_dec_ref(v___f_7898_);
lean_dec_ref(v___x_7879_);
v_val_7899_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7896_, 0);
lean_inc(v_val_7899_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_7896_);
v___y_7881_ = v_macosxDeploymentTarget_x3f_7896_;
v_val_7882_ = v_val_7899_;
goto v___jp_7880_;
}
else
{
lean_dec_ref(v___x_7877_);
lean_dec(v_buildTime_7872_);
lean_dec_ref(v_log_7868_);
lean_dec_ref(v_linker_7824_);
lean_dec_ref(v_args_7823_);
lean_dec_ref(v_linkObjs_7821_);
v___y_7836_ = v___f_7898_;
v___y_7837_ = v_a_7828_;
v___y_7838_ = v_a_7829_;
v___y_7839_ = v_a_7830_;
v___y_7840_ = v_a_7831_;
v___y_7841_ = v_a_7832_;
v___y_7842_ = v___x_7879_;
goto v___jp_7835_;
}
}
else
{
lean_object* v_val_7900_; 
lean_dec_ref(v___x_7879_);
v_val_7900_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7827_, 0);
lean_inc(v_val_7900_);
v___y_7881_ = v_macosxDeploymentTarget_x3f_7827_;
v_val_7882_ = v_val_7900_;
goto v___jp_7880_;
}
v___jp_7880_:
{
lean_object* v___x_7883_; lean_object* v___f_7884_; uint64_t v___x_7885_; uint64_t v___x_7886_; uint64_t v___x_7887_; lean_object* v___x_7888_; lean_object* v___x_7889_; lean_object* v___x_7890_; lean_object* v___x_7891_; lean_object* v___x_7892_; lean_object* v___x_7893_; lean_object* v___x_7894_; 
v___x_7883_ = lean_box(v_linkDeps_7826_);
lean_inc_ref(v_linkLibs_7822_);
lean_inc_ref(v_libFile_7820_);
v___f_7884_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7884_, 0, v_linkObjs_7821_);
lean_closure_set(v___f_7884_, 1, v_args_7823_);
lean_closure_set(v___f_7884_, 2, v_libFile_7820_);
lean_closure_set(v___f_7884_, 3, v_linker_7824_);
lean_closure_set(v___f_7884_, 4, v___y_7881_);
lean_closure_set(v___f_7884_, 5, v___x_7883_);
lean_closure_set(v___f_7884_, 6, v_linkLibs_7822_);
v___x_7885_ = l_Lake_Hash_nil;
v___x_7886_ = lean_string_hash(v_val_7882_);
v___x_7887_ = lean_uint64_mix_hash(v___x_7885_, v___x_7886_);
v___x_7888_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_7889_ = lean_string_append(v___x_7888_, v_val_7882_);
lean_dec_ref(v_val_7882_);
v___x_7890_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7891_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7892_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7892_, 0, v___x_7889_);
lean_ctor_set(v___x_7892_, 1, v___x_7890_);
lean_ctor_set(v___x_7892_, 2, v___x_7891_);
lean_ctor_set_uint64(v___x_7892_, sizeof(void*)*3, v___x_7887_);
v___x_7893_ = l_Lake_BuildTrace_mix(v___x_7877_, v___x_7892_);
v___x_7894_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_7894_, 0, v_log_7868_);
lean_ctor_set(v___x_7894_, 1, v___x_7893_);
lean_ctor_set(v___x_7894_, 2, v_buildTime_7872_);
lean_ctor_set_uint8(v___x_7894_, sizeof(void*)*3, v_action_7869_);
lean_ctor_set_uint8(v___x_7894_, sizeof(void*)*3 + 1, v_wantsRebuild_7870_);
v___y_7836_ = v___f_7884_;
v___y_7837_ = v_a_7828_;
v___y_7838_ = v_a_7829_;
v___y_7839_ = v_a_7830_;
v___y_7840_ = v_a_7831_;
v___y_7841_ = v_a_7832_;
v___y_7842_ = v___x_7894_;
goto v___jp_7835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object* v_libName_7903_, lean_object* v_libFile_7904_, lean_object* v_linkObjs_7905_, lean_object* v_linkLibs_7906_, lean_object* v_args_7907_, lean_object* v_linker_7908_, lean_object* v_plugin_7909_, lean_object* v_linkDeps_7910_, lean_object* v_macosxDeploymentTarget_x3f_7911_, lean_object* v_a_7912_, lean_object* v_a_7913_, lean_object* v_a_7914_, lean_object* v_a_7915_, lean_object* v_a_7916_, lean_object* v_a_7917_, lean_object* v_a_7918_){
_start:
{
uint8_t v_plugin_boxed_7919_; uint8_t v_linkDeps_boxed_7920_; lean_object* v_res_7921_; 
v_plugin_boxed_7919_ = lean_unbox(v_plugin_7909_);
v_linkDeps_boxed_7920_ = lean_unbox(v_linkDeps_7910_);
v_res_7921_ = l_Lake_buildSharedLibSync(v_libName_7903_, v_libFile_7904_, v_linkObjs_7905_, v_linkLibs_7906_, v_args_7907_, v_linker_7908_, v_plugin_boxed_7919_, v_linkDeps_boxed_7920_, v_macosxDeploymentTarget_x3f_7911_, v_a_7912_, v_a_7913_, v_a_7914_, v_a_7915_, v_a_7916_, v_a_7917_);
lean_dec_ref(v_a_7916_);
lean_dec(v_a_7915_);
lean_dec(v_a_7914_);
lean_dec(v_a_7913_);
return v_res_7921_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_extraDepTrace_7922_, lean_object* v_traceArgs_7923_, lean_object* v_weakArgs_7924_, lean_object* v_libName_7925_, lean_object* v_libFile_7926_, lean_object* v_objs_7927_, lean_object* v_linker_7928_, uint8_t v_plugin_7929_, uint8_t v_linkDeps_7930_, lean_object* v_macosxDeploymentTarget_x3f_7931_, lean_object* v_libs_7932_, lean_object* v___y_7933_, lean_object* v___y_7934_, lean_object* v___y_7935_, lean_object* v___y_7936_, lean_object* v___y_7937_, lean_object* v___y_7938_){
_start:
{
lean_object* v___x_7940_; 
lean_inc_ref(v___y_7937_);
lean_inc(v___y_7936_);
lean_inc(v___y_7935_);
lean_inc(v___y_7934_);
lean_inc_ref(v___y_7933_);
v___x_7940_ = lean_apply_7(v_extraDepTrace_7922_, v___y_7933_, v___y_7934_, v___y_7935_, v___y_7936_, v___y_7937_, v___y_7938_, lean_box(0));
if (lean_obj_tag(v___x_7940_) == 0)
{
lean_object* v_a_7941_; lean_object* v_a_7942_; lean_object* v_log_7943_; uint8_t v_action_7944_; uint8_t v_wantsRebuild_7945_; lean_object* v_trace_7946_; lean_object* v_buildTime_7947_; lean_object* v___x_7949_; uint8_t v_isShared_7950_; uint8_t v_isSharedCheck_7980_; 
v_a_7941_ = lean_ctor_get(v___x_7940_, 1);
lean_inc(v_a_7941_);
v_a_7942_ = lean_ctor_get(v___x_7940_, 0);
lean_inc(v_a_7942_);
lean_dec_ref_known(v___x_7940_, 2);
v_log_7943_ = lean_ctor_get(v_a_7941_, 0);
v_action_7944_ = lean_ctor_get_uint8(v_a_7941_, sizeof(void*)*3);
v_wantsRebuild_7945_ = lean_ctor_get_uint8(v_a_7941_, sizeof(void*)*3 + 1);
v_trace_7946_ = lean_ctor_get(v_a_7941_, 1);
v_buildTime_7947_ = lean_ctor_get(v_a_7941_, 2);
v_isSharedCheck_7980_ = !lean_is_exclusive(v_a_7941_);
if (v_isSharedCheck_7980_ == 0)
{
v___x_7949_ = v_a_7941_;
v_isShared_7950_ = v_isSharedCheck_7980_;
goto v_resetjp_7948_;
}
else
{
lean_inc(v_buildTime_7947_);
lean_inc(v_trace_7946_);
lean_inc(v_log_7943_);
lean_dec(v_a_7941_);
v___x_7949_ = lean_box(0);
v_isShared_7950_ = v_isSharedCheck_7980_;
goto v_resetjp_7948_;
}
v_resetjp_7948_:
{
lean_object* v___x_7951_; uint64_t v___y_7953_; uint64_t v___x_7969_; lean_object* v___x_7970_; lean_object* v___x_7971_; uint8_t v___x_7972_; 
v___x_7951_ = l_Lake_BuildTrace_mix(v_trace_7946_, v_a_7942_);
v___x_7969_ = l_Lake_Hash_nil;
v___x_7970_ = lean_unsigned_to_nat(0u);
v___x_7971_ = lean_array_get_size(v_traceArgs_7923_);
v___x_7972_ = lean_nat_dec_lt(v___x_7970_, v___x_7971_);
if (v___x_7972_ == 0)
{
v___y_7953_ = v___x_7969_;
goto v___jp_7952_;
}
else
{
uint8_t v___x_7973_; 
v___x_7973_ = lean_nat_dec_le(v___x_7971_, v___x_7971_);
if (v___x_7973_ == 0)
{
if (v___x_7972_ == 0)
{
v___y_7953_ = v___x_7969_;
goto v___jp_7952_;
}
else
{
size_t v___x_7974_; size_t v___x_7975_; uint64_t v___x_7976_; 
v___x_7974_ = ((size_t)0ULL);
v___x_7975_ = lean_usize_of_nat(v___x_7971_);
v___x_7976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7923_, v___x_7974_, v___x_7975_, v___x_7969_);
v___y_7953_ = v___x_7976_;
goto v___jp_7952_;
}
}
else
{
size_t v___x_7977_; size_t v___x_7978_; uint64_t v___x_7979_; 
v___x_7977_ = ((size_t)0ULL);
v___x_7978_ = lean_usize_of_nat(v___x_7971_);
v___x_7979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7923_, v___x_7977_, v___x_7978_, v___x_7969_);
v___y_7953_ = v___x_7979_;
goto v___jp_7952_;
}
}
v___jp_7952_:
{
lean_object* v___x_7954_; lean_object* v___x_7955_; lean_object* v___x_7956_; lean_object* v___x_7957_; lean_object* v___x_7958_; lean_object* v___x_7959_; lean_object* v___x_7960_; lean_object* v___x_7961_; lean_object* v___x_7962_; lean_object* v___x_7963_; lean_object* v___x_7965_; 
v___x_7954_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7955_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_7923_);
v___x_7956_ = lean_array_to_list(v_traceArgs_7923_);
v___x_7957_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7956_);
lean_dec(v___x_7956_);
v___x_7958_ = lean_string_append(v___x_7955_, v___x_7957_);
lean_dec_ref(v___x_7957_);
v___x_7959_ = lean_string_append(v___x_7954_, v___x_7958_);
lean_dec_ref(v___x_7958_);
v___x_7960_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7961_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7962_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7962_, 0, v___x_7959_);
lean_ctor_set(v___x_7962_, 1, v___x_7960_);
lean_ctor_set(v___x_7962_, 2, v___x_7961_);
lean_ctor_set_uint64(v___x_7962_, sizeof(void*)*3, v___y_7953_);
v___x_7963_ = l_Lake_BuildTrace_mix(v___x_7951_, v___x_7962_);
if (v_isShared_7950_ == 0)
{
lean_ctor_set(v___x_7949_, 1, v___x_7963_);
v___x_7965_ = v___x_7949_;
goto v_reusejp_7964_;
}
else
{
lean_object* v_reuseFailAlloc_7968_; 
v_reuseFailAlloc_7968_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7968_, 0, v_log_7943_);
lean_ctor_set(v_reuseFailAlloc_7968_, 1, v___x_7963_);
lean_ctor_set(v_reuseFailAlloc_7968_, 2, v_buildTime_7947_);
lean_ctor_set_uint8(v_reuseFailAlloc_7968_, sizeof(void*)*3, v_action_7944_);
lean_ctor_set_uint8(v_reuseFailAlloc_7968_, sizeof(void*)*3 + 1, v_wantsRebuild_7945_);
v___x_7965_ = v_reuseFailAlloc_7968_;
goto v_reusejp_7964_;
}
v_reusejp_7964_:
{
lean_object* v___x_7966_; lean_object* v___x_7967_; 
v___x_7966_ = l_Array_append___redArg(v_weakArgs_7924_, v_traceArgs_7923_);
lean_dec_ref(v_traceArgs_7923_);
v___x_7967_ = l_Lake_buildSharedLibSync(v_libName_7925_, v_libFile_7926_, v_objs_7927_, v_libs_7932_, v___x_7966_, v_linker_7928_, v_plugin_7929_, v_linkDeps_7930_, v_macosxDeploymentTarget_x3f_7931_, v___y_7933_, v___y_7934_, v___y_7935_, v___y_7936_, v___y_7937_, v___x_7965_);
return v___x_7967_;
}
}
}
}
else
{
lean_object* v_a_7981_; lean_object* v_a_7982_; lean_object* v___x_7984_; uint8_t v_isShared_7985_; uint8_t v_isSharedCheck_7989_; 
lean_dec_ref(v___y_7933_);
lean_dec_ref(v_libs_7932_);
lean_dec(v_macosxDeploymentTarget_x3f_7931_);
lean_dec_ref(v_linker_7928_);
lean_dec_ref(v_objs_7927_);
lean_dec_ref(v_libFile_7926_);
lean_dec_ref(v_libName_7925_);
lean_dec_ref(v_weakArgs_7924_);
lean_dec_ref(v_traceArgs_7923_);
v_a_7981_ = lean_ctor_get(v___x_7940_, 0);
v_a_7982_ = lean_ctor_get(v___x_7940_, 1);
v_isSharedCheck_7989_ = !lean_is_exclusive(v___x_7940_);
if (v_isSharedCheck_7989_ == 0)
{
v___x_7984_ = v___x_7940_;
v_isShared_7985_ = v_isSharedCheck_7989_;
goto v_resetjp_7983_;
}
else
{
lean_inc(v_a_7982_);
lean_inc(v_a_7981_);
lean_dec(v___x_7940_);
v___x_7984_ = lean_box(0);
v_isShared_7985_ = v_isSharedCheck_7989_;
goto v_resetjp_7983_;
}
v_resetjp_7983_:
{
lean_object* v___x_7987_; 
if (v_isShared_7985_ == 0)
{
v___x_7987_ = v___x_7984_;
goto v_reusejp_7986_;
}
else
{
lean_object* v_reuseFailAlloc_7988_; 
v_reuseFailAlloc_7988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7988_, 0, v_a_7981_);
lean_ctor_set(v_reuseFailAlloc_7988_, 1, v_a_7982_);
v___x_7987_ = v_reuseFailAlloc_7988_;
goto v_reusejp_7986_;
}
v_reusejp_7986_:
{
return v___x_7987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object** _args){
lean_object* v_extraDepTrace_7990_ = _args[0];
lean_object* v_traceArgs_7991_ = _args[1];
lean_object* v_weakArgs_7992_ = _args[2];
lean_object* v_libName_7993_ = _args[3];
lean_object* v_libFile_7994_ = _args[4];
lean_object* v_objs_7995_ = _args[5];
lean_object* v_linker_7996_ = _args[6];
lean_object* v_plugin_7997_ = _args[7];
lean_object* v_linkDeps_7998_ = _args[8];
lean_object* v_macosxDeploymentTarget_x3f_7999_ = _args[9];
lean_object* v_libs_8000_ = _args[10];
lean_object* v___y_8001_ = _args[11];
lean_object* v___y_8002_ = _args[12];
lean_object* v___y_8003_ = _args[13];
lean_object* v___y_8004_ = _args[14];
lean_object* v___y_8005_ = _args[15];
lean_object* v___y_8006_ = _args[16];
lean_object* v___y_8007_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8008_; uint8_t v_linkDeps_boxed_8009_; lean_object* v_res_8010_; 
v_plugin_boxed_8008_ = lean_unbox(v_plugin_7997_);
v_linkDeps_boxed_8009_ = lean_unbox(v_linkDeps_7998_);
v_res_8010_ = l_Lake_buildSharedLib___lam__0(v_extraDepTrace_7990_, v_traceArgs_7991_, v_weakArgs_7992_, v_libName_7993_, v_libFile_7994_, v_objs_7995_, v_linker_7996_, v_plugin_boxed_8008_, v_linkDeps_boxed_8009_, v_macosxDeploymentTarget_x3f_7999_, v_libs_8000_, v___y_8001_, v___y_8002_, v___y_8003_, v___y_8004_, v___y_8005_, v___y_8006_);
lean_dec_ref(v___y_8005_);
lean_dec(v___y_8004_);
lean_dec(v___y_8003_);
lean_dec(v___y_8002_);
return v_res_8010_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object* v_extraDepTrace_8012_, lean_object* v_traceArgs_8013_, lean_object* v_weakArgs_8014_, lean_object* v_libName_8015_, lean_object* v_libFile_8016_, lean_object* v_linker_8017_, uint8_t v_plugin_8018_, uint8_t v_linkDeps_8019_, lean_object* v_macosxDeploymentTarget_x3f_8020_, lean_object* v_linkLibs_8021_, lean_object* v___x_8022_, lean_object* v_objs_8023_, lean_object* v___y_8024_, lean_object* v___y_8025_, lean_object* v___y_8026_, lean_object* v___y_8027_, lean_object* v___y_8028_, lean_object* v___y_8029_){
_start:
{
lean_object* v_trace_8031_; lean_object* v___x_8032_; lean_object* v___x_8033_; lean_object* v___f_8034_; lean_object* v___x_8035_; lean_object* v___x_8036_; lean_object* v___x_8037_; uint8_t v___x_8038_; lean_object* v___x_8039_; lean_object* v___x_8040_; 
v_trace_8031_ = lean_ctor_get(v___y_8029_, 1);
v___x_8032_ = lean_box(v_plugin_8018_);
v___x_8033_ = lean_box(v_linkDeps_8019_);
v___f_8034_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 18, 10);
lean_closure_set(v___f_8034_, 0, v_extraDepTrace_8012_);
lean_closure_set(v___f_8034_, 1, v_traceArgs_8013_);
lean_closure_set(v___f_8034_, 2, v_weakArgs_8014_);
lean_closure_set(v___f_8034_, 3, v_libName_8015_);
lean_closure_set(v___f_8034_, 4, v_libFile_8016_);
lean_closure_set(v___f_8034_, 5, v_objs_8023_);
lean_closure_set(v___f_8034_, 6, v_linker_8017_);
lean_closure_set(v___f_8034_, 7, v___x_8032_);
lean_closure_set(v___f_8034_, 8, v___x_8033_);
lean_closure_set(v___f_8034_, 9, v_macosxDeploymentTarget_x3f_8020_);
v___x_8035_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8036_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8021_, v___x_8035_);
v___x_8037_ = lean_unsigned_to_nat(0u);
v___x_8038_ = 0;
v___x_8039_ = l_Lake_Job_mapM___redArg(v___x_8022_, v___x_8036_, v___f_8034_, v___x_8037_, v___x_8038_, v___y_8024_, v___y_8025_, v___y_8026_, v___y_8027_, v___y_8028_, v_trace_8031_);
v___x_8040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8040_, 0, v___x_8039_);
lean_ctor_set(v___x_8040_, 1, v___y_8029_);
return v___x_8040_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8041_ = _args[0];
lean_object* v_traceArgs_8042_ = _args[1];
lean_object* v_weakArgs_8043_ = _args[2];
lean_object* v_libName_8044_ = _args[3];
lean_object* v_libFile_8045_ = _args[4];
lean_object* v_linker_8046_ = _args[5];
lean_object* v_plugin_8047_ = _args[6];
lean_object* v_linkDeps_8048_ = _args[7];
lean_object* v_macosxDeploymentTarget_x3f_8049_ = _args[8];
lean_object* v_linkLibs_8050_ = _args[9];
lean_object* v___x_8051_ = _args[10];
lean_object* v_objs_8052_ = _args[11];
lean_object* v___y_8053_ = _args[12];
lean_object* v___y_8054_ = _args[13];
lean_object* v___y_8055_ = _args[14];
lean_object* v___y_8056_ = _args[15];
lean_object* v___y_8057_ = _args[16];
lean_object* v___y_8058_ = _args[17];
lean_object* v___y_8059_ = _args[18];
_start:
{
uint8_t v_plugin_boxed_8060_; uint8_t v_linkDeps_boxed_8061_; lean_object* v_res_8062_; 
v_plugin_boxed_8060_ = lean_unbox(v_plugin_8047_);
v_linkDeps_boxed_8061_ = lean_unbox(v_linkDeps_8048_);
v_res_8062_ = l_Lake_buildSharedLib___lam__1(v_extraDepTrace_8041_, v_traceArgs_8042_, v_weakArgs_8043_, v_libName_8044_, v_libFile_8045_, v_linker_8046_, v_plugin_boxed_8060_, v_linkDeps_boxed_8061_, v_macosxDeploymentTarget_x3f_8049_, v_linkLibs_8050_, v___x_8051_, v_objs_8052_, v___y_8053_, v___y_8054_, v___y_8055_, v___y_8056_, v___y_8057_, v___y_8058_);
lean_dec_ref(v___y_8057_);
lean_dec(v___y_8056_);
lean_dec(v___y_8055_);
lean_dec(v___y_8054_);
lean_dec_ref(v_linkLibs_8050_);
return v_res_8062_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_8064_, lean_object* v_libFile_8065_, lean_object* v_linkObjs_8066_, lean_object* v_linkLibs_8067_, lean_object* v_weakArgs_8068_, lean_object* v_traceArgs_8069_, lean_object* v_linker_8070_, lean_object* v_extraDepTrace_8071_, uint8_t v_plugin_8072_, uint8_t v_linkDeps_8073_, lean_object* v_macosxDeploymentTarget_x3f_8074_, lean_object* v_a_8075_, lean_object* v_a_8076_, lean_object* v_a_8077_, lean_object* v_a_8078_, lean_object* v_a_8079_, lean_object* v_a_8080_){
_start:
{
lean_object* v___x_8082_; lean_object* v___x_8083_; lean_object* v___x_8084_; lean_object* v___f_8085_; lean_object* v___x_8086_; lean_object* v___x_8087_; lean_object* v___x_8088_; uint8_t v___x_8089_; lean_object* v___x_8090_; 
v___x_8082_ = l_Lake_instDataKindDynlib;
v___x_8083_ = lean_box(v_plugin_8072_);
v___x_8084_ = lean_box(v_linkDeps_8073_);
v___f_8085_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 19, 11);
lean_closure_set(v___f_8085_, 0, v_extraDepTrace_8071_);
lean_closure_set(v___f_8085_, 1, v_traceArgs_8069_);
lean_closure_set(v___f_8085_, 2, v_weakArgs_8068_);
lean_closure_set(v___f_8085_, 3, v_libName_8064_);
lean_closure_set(v___f_8085_, 4, v_libFile_8065_);
lean_closure_set(v___f_8085_, 5, v_linker_8070_);
lean_closure_set(v___f_8085_, 6, v___x_8083_);
lean_closure_set(v___f_8085_, 7, v___x_8084_);
lean_closure_set(v___f_8085_, 8, v_macosxDeploymentTarget_x3f_8074_);
lean_closure_set(v___f_8085_, 9, v_linkLibs_8067_);
lean_closure_set(v___f_8085_, 10, v___x_8082_);
v___x_8086_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8087_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8066_, v___x_8086_);
v___x_8088_ = lean_unsigned_to_nat(0u);
v___x_8089_ = 1;
v___x_8090_ = l_Lake_Job_bindM___redArg(v___x_8082_, v___x_8087_, v___f_8085_, v___x_8088_, v___x_8089_, v_a_8075_, v_a_8076_, v_a_8077_, v_a_8078_, v_a_8079_, v_a_8080_);
return v___x_8090_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_8091_ = _args[0];
lean_object* v_libFile_8092_ = _args[1];
lean_object* v_linkObjs_8093_ = _args[2];
lean_object* v_linkLibs_8094_ = _args[3];
lean_object* v_weakArgs_8095_ = _args[4];
lean_object* v_traceArgs_8096_ = _args[5];
lean_object* v_linker_8097_ = _args[6];
lean_object* v_extraDepTrace_8098_ = _args[7];
lean_object* v_plugin_8099_ = _args[8];
lean_object* v_linkDeps_8100_ = _args[9];
lean_object* v_macosxDeploymentTarget_x3f_8101_ = _args[10];
lean_object* v_a_8102_ = _args[11];
lean_object* v_a_8103_ = _args[12];
lean_object* v_a_8104_ = _args[13];
lean_object* v_a_8105_ = _args[14];
lean_object* v_a_8106_ = _args[15];
lean_object* v_a_8107_ = _args[16];
lean_object* v_a_8108_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8109_; uint8_t v_linkDeps_boxed_8110_; lean_object* v_res_8111_; 
v_plugin_boxed_8109_ = lean_unbox(v_plugin_8099_);
v_linkDeps_boxed_8110_ = lean_unbox(v_linkDeps_8100_);
v_res_8111_ = l_Lake_buildSharedLib(v_libName_8091_, v_libFile_8092_, v_linkObjs_8093_, v_linkLibs_8094_, v_weakArgs_8095_, v_traceArgs_8096_, v_linker_8097_, v_extraDepTrace_8098_, v_plugin_boxed_8109_, v_linkDeps_boxed_8110_, v_macosxDeploymentTarget_x3f_8101_, v_a_8102_, v_a_8103_, v_a_8104_, v_a_8105_, v_a_8106_, v_a_8107_);
lean_dec_ref(v_a_8107_);
lean_dec_ref(v_a_8106_);
lean_dec(v_a_8105_);
lean_dec(v_a_8104_);
lean_dec(v_a_8103_);
lean_dec_ref(v_linkObjs_8093_);
return v_res_8111_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object* v_linkObjs_8112_, lean_object* v_args_8113_, uint8_t v___x_8114_, lean_object* v_libFile_8115_, lean_object* v_macosxDeploymentTarget_x3f_8116_, uint8_t v_linkDeps_8117_, lean_object* v_linkLibs_8118_, lean_object* v___y_8119_, lean_object* v___y_8120_, lean_object* v___y_8121_, lean_object* v___y_8122_, lean_object* v___y_8123_, lean_object* v___y_8124_){
_start:
{
lean_object* v_toContext_8126_; lean_object* v_lakeEnv_8127_; lean_object* v_lean_8128_; lean_object* v_libs_8130_; lean_object* v___y_8131_; 
v_toContext_8126_ = lean_ctor_get(v___y_8123_, 1);
v_lakeEnv_8127_ = lean_ctor_get(v_toContext_8126_, 0);
v_lean_8128_ = lean_ctor_get(v_lakeEnv_8127_, 1);
if (v_linkDeps_8117_ == 0)
{
lean_object* v___x_8177_; 
v___x_8177_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_8130_ = v___x_8177_;
v___y_8131_ = v___y_8124_;
goto v___jp_8129_;
}
else
{
lean_object* v___x_8178_; 
v___x_8178_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8118_, v___y_8124_);
if (lean_obj_tag(v___x_8178_) == 0)
{
lean_object* v_a_8179_; lean_object* v_a_8180_; 
v_a_8179_ = lean_ctor_get(v___x_8178_, 0);
lean_inc(v_a_8179_);
v_a_8180_ = lean_ctor_get(v___x_8178_, 1);
lean_inc(v_a_8180_);
lean_dec_ref_known(v___x_8178_, 2);
v_libs_8130_ = v_a_8179_;
v___y_8131_ = v_a_8180_;
goto v___jp_8129_;
}
else
{
lean_object* v_a_8181_; lean_object* v_a_8182_; lean_object* v___x_8184_; uint8_t v_isShared_8185_; uint8_t v_isSharedCheck_8189_; 
lean_dec(v_macosxDeploymentTarget_x3f_8116_);
lean_dec_ref(v_libFile_8115_);
v_a_8181_ = lean_ctor_get(v___x_8178_, 0);
v_a_8182_ = lean_ctor_get(v___x_8178_, 1);
v_isSharedCheck_8189_ = !lean_is_exclusive(v___x_8178_);
if (v_isSharedCheck_8189_ == 0)
{
v___x_8184_ = v___x_8178_;
v_isShared_8185_ = v_isSharedCheck_8189_;
goto v_resetjp_8183_;
}
else
{
lean_inc(v_a_8182_);
lean_inc(v_a_8181_);
lean_dec(v___x_8178_);
v___x_8184_ = lean_box(0);
v_isShared_8185_ = v_isSharedCheck_8189_;
goto v_resetjp_8183_;
}
v_resetjp_8183_:
{
lean_object* v___x_8187_; 
if (v_isShared_8185_ == 0)
{
v___x_8187_ = v___x_8184_;
goto v_reusejp_8186_;
}
else
{
lean_object* v_reuseFailAlloc_8188_; 
v_reuseFailAlloc_8188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8188_, 0, v_a_8181_);
lean_ctor_set(v_reuseFailAlloc_8188_, 1, v_a_8182_);
v___x_8187_ = v_reuseFailAlloc_8188_;
goto v_reusejp_8186_;
}
v_reusejp_8186_:
{
return v___x_8187_;
}
}
}
}
v___jp_8129_:
{
lean_object* v_leanLibDir_8132_; lean_object* v_cc_8133_; lean_object* v_log_8134_; uint8_t v_action_8135_; uint8_t v_wantsRebuild_8136_; lean_object* v_trace_8137_; lean_object* v_buildTime_8138_; lean_object* v___x_8140_; uint8_t v_isShared_8141_; uint8_t v_isSharedCheck_8176_; 
v_leanLibDir_8132_ = lean_ctor_get(v_lean_8128_, 3);
v_cc_8133_ = lean_ctor_get(v_lean_8128_, 14);
v_log_8134_ = lean_ctor_get(v___y_8131_, 0);
v_action_8135_ = lean_ctor_get_uint8(v___y_8131_, sizeof(void*)*3);
v_wantsRebuild_8136_ = lean_ctor_get_uint8(v___y_8131_, sizeof(void*)*3 + 1);
v_trace_8137_ = lean_ctor_get(v___y_8131_, 1);
v_buildTime_8138_ = lean_ctor_get(v___y_8131_, 2);
v_isSharedCheck_8176_ = !lean_is_exclusive(v___y_8131_);
if (v_isSharedCheck_8176_ == 0)
{
v___x_8140_ = v___y_8131_;
v_isShared_8141_ = v_isSharedCheck_8176_;
goto v_resetjp_8139_;
}
else
{
lean_inc(v_buildTime_8138_);
lean_inc(v_trace_8137_);
lean_inc(v_log_8134_);
lean_dec(v___y_8131_);
v___x_8140_ = lean_box(0);
v_isShared_8141_ = v_isSharedCheck_8176_;
goto v_resetjp_8139_;
}
v_resetjp_8139_:
{
lean_object* v___x_8142_; lean_object* v___x_8143_; lean_object* v___x_8144_; lean_object* v___x_8145_; lean_object* v___x_8146_; lean_object* v___x_8147_; lean_object* v___x_8148_; lean_object* v___x_8149_; lean_object* v___x_8150_; lean_object* v___x_8151_; 
v___x_8142_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8112_, v_libs_8130_);
lean_dec_ref(v_libs_8130_);
v___x_8143_ = l_Array_append___redArg(v___x_8142_, v_args_8113_);
v___x_8144_ = lean_unsigned_to_nat(2u);
v___x_8145_ = lean_mk_empty_array_with_capacity(v___x_8144_);
lean_dec_ref(v___x_8145_);
v___x_8146_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8132_);
v___x_8147_ = lean_array_push(v___x_8146_, v_leanLibDir_8132_);
v___x_8148_ = l_Array_append___redArg(v___x_8143_, v___x_8147_);
lean_dec_ref(v___x_8147_);
v___x_8149_ = l_Lake_LeanInstall_ccLinkFlags(v___x_8114_, v_lean_8128_);
v___x_8150_ = l_Array_append___redArg(v___x_8148_, v___x_8149_);
lean_dec_ref(v___x_8149_);
lean_inc_ref(v_cc_8133_);
v___x_8151_ = l_Lake_compileSharedLib(v_libFile_8115_, v___x_8150_, v_cc_8133_, v_macosxDeploymentTarget_x3f_8116_, v_log_8134_);
lean_dec_ref(v___x_8150_);
if (lean_obj_tag(v___x_8151_) == 0)
{
lean_object* v_a_8152_; lean_object* v_a_8153_; lean_object* v___x_8155_; uint8_t v_isShared_8156_; uint8_t v_isSharedCheck_8163_; 
v_a_8152_ = lean_ctor_get(v___x_8151_, 0);
v_a_8153_ = lean_ctor_get(v___x_8151_, 1);
v_isSharedCheck_8163_ = !lean_is_exclusive(v___x_8151_);
if (v_isSharedCheck_8163_ == 0)
{
v___x_8155_ = v___x_8151_;
v_isShared_8156_ = v_isSharedCheck_8163_;
goto v_resetjp_8154_;
}
else
{
lean_inc(v_a_8153_);
lean_inc(v_a_8152_);
lean_dec(v___x_8151_);
v___x_8155_ = lean_box(0);
v_isShared_8156_ = v_isSharedCheck_8163_;
goto v_resetjp_8154_;
}
v_resetjp_8154_:
{
lean_object* v___x_8158_; 
if (v_isShared_8141_ == 0)
{
lean_ctor_set(v___x_8140_, 0, v_a_8153_);
v___x_8158_ = v___x_8140_;
goto v_reusejp_8157_;
}
else
{
lean_object* v_reuseFailAlloc_8162_; 
v_reuseFailAlloc_8162_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8162_, 0, v_a_8153_);
lean_ctor_set(v_reuseFailAlloc_8162_, 1, v_trace_8137_);
lean_ctor_set(v_reuseFailAlloc_8162_, 2, v_buildTime_8138_);
lean_ctor_set_uint8(v_reuseFailAlloc_8162_, sizeof(void*)*3, v_action_8135_);
lean_ctor_set_uint8(v_reuseFailAlloc_8162_, sizeof(void*)*3 + 1, v_wantsRebuild_8136_);
v___x_8158_ = v_reuseFailAlloc_8162_;
goto v_reusejp_8157_;
}
v_reusejp_8157_:
{
lean_object* v___x_8160_; 
if (v_isShared_8156_ == 0)
{
lean_ctor_set(v___x_8155_, 1, v___x_8158_);
v___x_8160_ = v___x_8155_;
goto v_reusejp_8159_;
}
else
{
lean_object* v_reuseFailAlloc_8161_; 
v_reuseFailAlloc_8161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8161_, 0, v_a_8152_);
lean_ctor_set(v_reuseFailAlloc_8161_, 1, v___x_8158_);
v___x_8160_ = v_reuseFailAlloc_8161_;
goto v_reusejp_8159_;
}
v_reusejp_8159_:
{
return v___x_8160_;
}
}
}
}
else
{
lean_object* v_a_8164_; lean_object* v_a_8165_; lean_object* v___x_8167_; uint8_t v_isShared_8168_; uint8_t v_isSharedCheck_8175_; 
v_a_8164_ = lean_ctor_get(v___x_8151_, 0);
v_a_8165_ = lean_ctor_get(v___x_8151_, 1);
v_isSharedCheck_8175_ = !lean_is_exclusive(v___x_8151_);
if (v_isSharedCheck_8175_ == 0)
{
v___x_8167_ = v___x_8151_;
v_isShared_8168_ = v_isSharedCheck_8175_;
goto v_resetjp_8166_;
}
else
{
lean_inc(v_a_8165_);
lean_inc(v_a_8164_);
lean_dec(v___x_8151_);
v___x_8167_ = lean_box(0);
v_isShared_8168_ = v_isSharedCheck_8175_;
goto v_resetjp_8166_;
}
v_resetjp_8166_:
{
lean_object* v___x_8170_; 
if (v_isShared_8141_ == 0)
{
lean_ctor_set(v___x_8140_, 0, v_a_8165_);
v___x_8170_ = v___x_8140_;
goto v_reusejp_8169_;
}
else
{
lean_object* v_reuseFailAlloc_8174_; 
v_reuseFailAlloc_8174_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8174_, 0, v_a_8165_);
lean_ctor_set(v_reuseFailAlloc_8174_, 1, v_trace_8137_);
lean_ctor_set(v_reuseFailAlloc_8174_, 2, v_buildTime_8138_);
lean_ctor_set_uint8(v_reuseFailAlloc_8174_, sizeof(void*)*3, v_action_8135_);
lean_ctor_set_uint8(v_reuseFailAlloc_8174_, sizeof(void*)*3 + 1, v_wantsRebuild_8136_);
v___x_8170_ = v_reuseFailAlloc_8174_;
goto v_reusejp_8169_;
}
v_reusejp_8169_:
{
lean_object* v___x_8172_; 
if (v_isShared_8168_ == 0)
{
lean_ctor_set(v___x_8167_, 1, v___x_8170_);
v___x_8172_ = v___x_8167_;
goto v_reusejp_8171_;
}
else
{
lean_object* v_reuseFailAlloc_8173_; 
v_reuseFailAlloc_8173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8173_, 0, v_a_8164_);
lean_ctor_set(v_reuseFailAlloc_8173_, 1, v___x_8170_);
v___x_8172_ = v_reuseFailAlloc_8173_;
goto v_reusejp_8171_;
}
v_reusejp_8171_:
{
return v___x_8172_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_8190_, lean_object* v_args_8191_, lean_object* v___x_8192_, lean_object* v_libFile_8193_, lean_object* v_macosxDeploymentTarget_x3f_8194_, lean_object* v_linkDeps_8195_, lean_object* v_linkLibs_8196_, lean_object* v___y_8197_, lean_object* v___y_8198_, lean_object* v___y_8199_, lean_object* v___y_8200_, lean_object* v___y_8201_, lean_object* v___y_8202_, lean_object* v___y_8203_){
_start:
{
uint8_t v___x_34592__boxed_8204_; uint8_t v_linkDeps_boxed_8205_; lean_object* v_res_8206_; 
v___x_34592__boxed_8204_ = lean_unbox(v___x_8192_);
v_linkDeps_boxed_8205_ = lean_unbox(v_linkDeps_8195_);
v_res_8206_ = l_Lake_buildLeanSharedLibSync___lam__0(v_linkObjs_8190_, v_args_8191_, v___x_34592__boxed_8204_, v_libFile_8193_, v_macosxDeploymentTarget_x3f_8194_, v_linkDeps_boxed_8205_, v_linkLibs_8196_, v___y_8197_, v___y_8198_, v___y_8199_, v___y_8200_, v___y_8201_, v___y_8202_);
lean_dec_ref(v___y_8201_);
lean_dec(v___y_8200_);
lean_dec(v___y_8199_);
lean_dec(v___y_8198_);
lean_dec_ref(v___y_8197_);
lean_dec_ref(v_linkLibs_8196_);
lean_dec_ref(v_args_8191_);
lean_dec_ref(v_linkObjs_8190_);
return v_res_8206_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object* v_libName_8207_, lean_object* v_libFile_8208_, lean_object* v_linkObjs_8209_, lean_object* v_linkLibs_8210_, lean_object* v_args_8211_, uint8_t v_plugin_8212_, uint8_t v_linkDeps_8213_, lean_object* v_macosxDeploymentTarget_x3f_8214_, lean_object* v_a_8215_, lean_object* v_a_8216_, lean_object* v_a_8217_, lean_object* v_a_8218_, lean_object* v_a_8219_, lean_object* v_a_8220_){
_start:
{
lean_object* v_log_8222_; uint8_t v_action_8223_; uint8_t v_wantsRebuild_8224_; lean_object* v_trace_8225_; lean_object* v_buildTime_8226_; lean_object* v___x_8228_; uint8_t v_isShared_8229_; uint8_t v_isSharedCheck_8265_; 
v_log_8222_ = lean_ctor_get(v_a_8220_, 0);
v_action_8223_ = lean_ctor_get_uint8(v_a_8220_, sizeof(void*)*3);
v_wantsRebuild_8224_ = lean_ctor_get_uint8(v_a_8220_, sizeof(void*)*3 + 1);
v_trace_8225_ = lean_ctor_get(v_a_8220_, 1);
v_buildTime_8226_ = lean_ctor_get(v_a_8220_, 2);
v_isSharedCheck_8265_ = !lean_is_exclusive(v_a_8220_);
if (v_isSharedCheck_8265_ == 0)
{
v___x_8228_ = v_a_8220_;
v_isShared_8229_ = v_isSharedCheck_8265_;
goto v_resetjp_8227_;
}
else
{
lean_inc(v_buildTime_8226_);
lean_inc(v_trace_8225_);
lean_inc(v_log_8222_);
lean_dec(v_a_8220_);
v___x_8228_ = lean_box(0);
v_isShared_8229_ = v_isSharedCheck_8265_;
goto v_resetjp_8227_;
}
v_resetjp_8227_:
{
lean_object* v_leanTrace_8230_; lean_object* v___x_8231_; lean_object* v___x_8232_; lean_object* v___x_8233_; lean_object* v___x_8235_; 
v_leanTrace_8230_ = lean_ctor_get(v_a_8219_, 2);
lean_inc_ref(v_leanTrace_8230_);
v___x_8231_ = l_Lake_BuildTrace_mix(v_trace_8225_, v_leanTrace_8230_);
v___x_8232_ = l_Lake_platformTrace;
v___x_8233_ = l_Lake_BuildTrace_mix(v___x_8231_, v___x_8232_);
if (v_isShared_8229_ == 0)
{
lean_ctor_set(v___x_8228_, 1, v___x_8233_);
v___x_8235_ = v___x_8228_;
goto v_reusejp_8234_;
}
else
{
lean_object* v_reuseFailAlloc_8264_; 
v_reuseFailAlloc_8264_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8264_, 0, v_log_8222_);
lean_ctor_set(v_reuseFailAlloc_8264_, 1, v___x_8233_);
lean_ctor_set(v_reuseFailAlloc_8264_, 2, v_buildTime_8226_);
lean_ctor_set_uint8(v_reuseFailAlloc_8264_, sizeof(void*)*3, v_action_8223_);
lean_ctor_set_uint8(v_reuseFailAlloc_8264_, sizeof(void*)*3 + 1, v_wantsRebuild_8224_);
v___x_8235_ = v_reuseFailAlloc_8264_;
goto v_reusejp_8234_;
}
v_reusejp_8234_:
{
uint8_t v___x_8236_; lean_object* v___x_8237_; lean_object* v___x_8238_; lean_object* v___f_8239_; uint8_t v___x_8240_; lean_object* v___x_8241_; lean_object* v___x_8242_; 
v___x_8236_ = 1;
v___x_8237_ = lean_box(v___x_8236_);
v___x_8238_ = lean_box(v_linkDeps_8213_);
lean_inc_ref(v_linkLibs_8210_);
lean_inc_ref(v_libFile_8208_);
v___f_8239_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_8239_, 0, v_linkObjs_8209_);
lean_closure_set(v___f_8239_, 1, v_args_8211_);
lean_closure_set(v___f_8239_, 2, v___x_8237_);
lean_closure_set(v___f_8239_, 3, v_libFile_8208_);
lean_closure_set(v___f_8239_, 4, v_macosxDeploymentTarget_x3f_8214_);
lean_closure_set(v___f_8239_, 5, v___x_8238_);
lean_closure_set(v___f_8239_, 6, v_linkLibs_8210_);
v___x_8240_ = 0;
v___x_8241_ = l_Lake_sharedLibExt;
v___x_8242_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8208_, v___f_8239_, v___x_8240_, v___x_8241_, v___x_8236_, v___x_8240_, v___x_8240_, v_a_8215_, v_a_8216_, v_a_8217_, v_a_8218_, v_a_8219_, v___x_8235_);
if (lean_obj_tag(v___x_8242_) == 0)
{
lean_object* v_a_8243_; lean_object* v_a_8244_; lean_object* v___x_8246_; uint8_t v_isShared_8247_; uint8_t v_isSharedCheck_8254_; 
v_a_8243_ = lean_ctor_get(v___x_8242_, 0);
v_a_8244_ = lean_ctor_get(v___x_8242_, 1);
v_isSharedCheck_8254_ = !lean_is_exclusive(v___x_8242_);
if (v_isSharedCheck_8254_ == 0)
{
v___x_8246_ = v___x_8242_;
v_isShared_8247_ = v_isSharedCheck_8254_;
goto v_resetjp_8245_;
}
else
{
lean_inc(v_a_8244_);
lean_inc(v_a_8243_);
lean_dec(v___x_8242_);
v___x_8246_ = lean_box(0);
v_isShared_8247_ = v_isSharedCheck_8254_;
goto v_resetjp_8245_;
}
v_resetjp_8245_:
{
lean_object* v_path_8248_; lean_object* v___x_8249_; lean_object* v___x_8250_; lean_object* v___x_8252_; 
v_path_8248_ = lean_ctor_get(v_a_8243_, 1);
lean_inc_ref(v_path_8248_);
lean_dec(v_a_8243_);
v___x_8249_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_8250_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8250_, 0, v_path_8248_);
lean_ctor_set(v___x_8250_, 1, v_libName_8207_);
lean_ctor_set(v___x_8250_, 2, v_linkLibs_8210_);
lean_ctor_set(v___x_8250_, 3, v___x_8249_);
lean_ctor_set_uint8(v___x_8250_, sizeof(void*)*4, v_plugin_8212_);
if (v_isShared_8247_ == 0)
{
lean_ctor_set(v___x_8246_, 0, v___x_8250_);
v___x_8252_ = v___x_8246_;
goto v_reusejp_8251_;
}
else
{
lean_object* v_reuseFailAlloc_8253_; 
v_reuseFailAlloc_8253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8253_, 0, v___x_8250_);
lean_ctor_set(v_reuseFailAlloc_8253_, 1, v_a_8244_);
v___x_8252_ = v_reuseFailAlloc_8253_;
goto v_reusejp_8251_;
}
v_reusejp_8251_:
{
return v___x_8252_;
}
}
}
else
{
lean_object* v_a_8255_; lean_object* v_a_8256_; lean_object* v___x_8258_; uint8_t v_isShared_8259_; uint8_t v_isSharedCheck_8263_; 
lean_dec_ref(v_linkLibs_8210_);
lean_dec_ref(v_libName_8207_);
v_a_8255_ = lean_ctor_get(v___x_8242_, 0);
v_a_8256_ = lean_ctor_get(v___x_8242_, 1);
v_isSharedCheck_8263_ = !lean_is_exclusive(v___x_8242_);
if (v_isSharedCheck_8263_ == 0)
{
v___x_8258_ = v___x_8242_;
v_isShared_8259_ = v_isSharedCheck_8263_;
goto v_resetjp_8257_;
}
else
{
lean_inc(v_a_8256_);
lean_inc(v_a_8255_);
lean_dec(v___x_8242_);
v___x_8258_ = lean_box(0);
v_isShared_8259_ = v_isSharedCheck_8263_;
goto v_resetjp_8257_;
}
v_resetjp_8257_:
{
lean_object* v___x_8261_; 
if (v_isShared_8259_ == 0)
{
v___x_8261_ = v___x_8258_;
goto v_reusejp_8260_;
}
else
{
lean_object* v_reuseFailAlloc_8262_; 
v_reuseFailAlloc_8262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8262_, 0, v_a_8255_);
lean_ctor_set(v_reuseFailAlloc_8262_, 1, v_a_8256_);
v___x_8261_ = v_reuseFailAlloc_8262_;
goto v_reusejp_8260_;
}
v_reusejp_8260_:
{
return v___x_8261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object* v_libName_8266_, lean_object* v_libFile_8267_, lean_object* v_linkObjs_8268_, lean_object* v_linkLibs_8269_, lean_object* v_args_8270_, lean_object* v_plugin_8271_, lean_object* v_linkDeps_8272_, lean_object* v_macosxDeploymentTarget_x3f_8273_, lean_object* v_a_8274_, lean_object* v_a_8275_, lean_object* v_a_8276_, lean_object* v_a_8277_, lean_object* v_a_8278_, lean_object* v_a_8279_, lean_object* v_a_8280_){
_start:
{
uint8_t v_plugin_boxed_8281_; uint8_t v_linkDeps_boxed_8282_; lean_object* v_res_8283_; 
v_plugin_boxed_8281_ = lean_unbox(v_plugin_8271_);
v_linkDeps_boxed_8282_ = lean_unbox(v_linkDeps_8272_);
v_res_8283_ = l_Lake_buildLeanSharedLibSync(v_libName_8266_, v_libFile_8267_, v_linkObjs_8268_, v_linkLibs_8269_, v_args_8270_, v_plugin_boxed_8281_, v_linkDeps_boxed_8282_, v_macosxDeploymentTarget_x3f_8273_, v_a_8274_, v_a_8275_, v_a_8276_, v_a_8277_, v_a_8278_, v_a_8279_);
lean_dec_ref(v_a_8278_);
lean_dec(v_a_8277_);
lean_dec(v_a_8276_);
lean_dec(v_a_8275_);
return v_res_8283_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_traceArgs_8284_, lean_object* v_weakArgs_8285_, lean_object* v_libName_8286_, lean_object* v_libFile_8287_, lean_object* v_objs_8288_, uint8_t v_plugin_8289_, uint8_t v_linkDeps_8290_, lean_object* v_macosxDeploymentTarget_x3f_8291_, lean_object* v_libs_8292_, lean_object* v___y_8293_, lean_object* v___y_8294_, lean_object* v___y_8295_, lean_object* v___y_8296_, lean_object* v___y_8297_, lean_object* v___y_8298_){
_start:
{
uint64_t v___y_8301_; uint64_t v___x_8326_; lean_object* v___x_8327_; lean_object* v___x_8328_; uint8_t v___x_8329_; 
v___x_8326_ = l_Lake_Hash_nil;
v___x_8327_ = lean_unsigned_to_nat(0u);
v___x_8328_ = lean_array_get_size(v_traceArgs_8284_);
v___x_8329_ = lean_nat_dec_lt(v___x_8327_, v___x_8328_);
if (v___x_8329_ == 0)
{
v___y_8301_ = v___x_8326_;
goto v___jp_8300_;
}
else
{
uint8_t v___x_8330_; 
v___x_8330_ = lean_nat_dec_le(v___x_8328_, v___x_8328_);
if (v___x_8330_ == 0)
{
if (v___x_8329_ == 0)
{
v___y_8301_ = v___x_8326_;
goto v___jp_8300_;
}
else
{
size_t v___x_8331_; size_t v___x_8332_; uint64_t v___x_8333_; 
v___x_8331_ = ((size_t)0ULL);
v___x_8332_ = lean_usize_of_nat(v___x_8328_);
v___x_8333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8284_, v___x_8331_, v___x_8332_, v___x_8326_);
v___y_8301_ = v___x_8333_;
goto v___jp_8300_;
}
}
else
{
size_t v___x_8334_; size_t v___x_8335_; uint64_t v___x_8336_; 
v___x_8334_ = ((size_t)0ULL);
v___x_8335_ = lean_usize_of_nat(v___x_8328_);
v___x_8336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8284_, v___x_8334_, v___x_8335_, v___x_8326_);
v___y_8301_ = v___x_8336_;
goto v___jp_8300_;
}
}
v___jp_8300_:
{
lean_object* v_log_8302_; uint8_t v_action_8303_; uint8_t v_wantsRebuild_8304_; lean_object* v_trace_8305_; lean_object* v_buildTime_8306_; lean_object* v___x_8308_; uint8_t v_isShared_8309_; uint8_t v_isSharedCheck_8325_; 
v_log_8302_ = lean_ctor_get(v___y_8298_, 0);
v_action_8303_ = lean_ctor_get_uint8(v___y_8298_, sizeof(void*)*3);
v_wantsRebuild_8304_ = lean_ctor_get_uint8(v___y_8298_, sizeof(void*)*3 + 1);
v_trace_8305_ = lean_ctor_get(v___y_8298_, 1);
v_buildTime_8306_ = lean_ctor_get(v___y_8298_, 2);
v_isSharedCheck_8325_ = !lean_is_exclusive(v___y_8298_);
if (v_isSharedCheck_8325_ == 0)
{
v___x_8308_ = v___y_8298_;
v_isShared_8309_ = v_isSharedCheck_8325_;
goto v_resetjp_8307_;
}
else
{
lean_inc(v_buildTime_8306_);
lean_inc(v_trace_8305_);
lean_inc(v_log_8302_);
lean_dec(v___y_8298_);
v___x_8308_ = lean_box(0);
v_isShared_8309_ = v_isSharedCheck_8325_;
goto v_resetjp_8307_;
}
v_resetjp_8307_:
{
lean_object* v___x_8310_; lean_object* v___x_8311_; lean_object* v___x_8312_; lean_object* v___x_8313_; lean_object* v___x_8314_; lean_object* v___x_8315_; lean_object* v___x_8316_; lean_object* v___x_8317_; lean_object* v___x_8318_; lean_object* v___x_8319_; lean_object* v___x_8321_; 
v___x_8310_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8311_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8312_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8284_);
v___x_8313_ = lean_array_to_list(v_traceArgs_8284_);
v___x_8314_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8313_);
lean_dec(v___x_8313_);
v___x_8315_ = lean_string_append(v___x_8312_, v___x_8314_);
lean_dec_ref(v___x_8314_);
v___x_8316_ = lean_string_append(v___x_8311_, v___x_8315_);
lean_dec_ref(v___x_8315_);
v___x_8317_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8318_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8318_, 0, v___x_8316_);
lean_ctor_set(v___x_8318_, 1, v___x_8310_);
lean_ctor_set(v___x_8318_, 2, v___x_8317_);
lean_ctor_set_uint64(v___x_8318_, sizeof(void*)*3, v___y_8301_);
v___x_8319_ = l_Lake_BuildTrace_mix(v_trace_8305_, v___x_8318_);
if (v_isShared_8309_ == 0)
{
lean_ctor_set(v___x_8308_, 1, v___x_8319_);
v___x_8321_ = v___x_8308_;
goto v_reusejp_8320_;
}
else
{
lean_object* v_reuseFailAlloc_8324_; 
v_reuseFailAlloc_8324_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8324_, 0, v_log_8302_);
lean_ctor_set(v_reuseFailAlloc_8324_, 1, v___x_8319_);
lean_ctor_set(v_reuseFailAlloc_8324_, 2, v_buildTime_8306_);
lean_ctor_set_uint8(v_reuseFailAlloc_8324_, sizeof(void*)*3, v_action_8303_);
lean_ctor_set_uint8(v_reuseFailAlloc_8324_, sizeof(void*)*3 + 1, v_wantsRebuild_8304_);
v___x_8321_ = v_reuseFailAlloc_8324_;
goto v_reusejp_8320_;
}
v_reusejp_8320_:
{
lean_object* v___x_8322_; lean_object* v___x_8323_; 
v___x_8322_ = l_Array_append___redArg(v_weakArgs_8285_, v_traceArgs_8284_);
lean_dec_ref(v_traceArgs_8284_);
v___x_8323_ = l_Lake_buildLeanSharedLibSync(v_libName_8286_, v_libFile_8287_, v_objs_8288_, v_libs_8292_, v___x_8322_, v_plugin_8289_, v_linkDeps_8290_, v_macosxDeploymentTarget_x3f_8291_, v___y_8293_, v___y_8294_, v___y_8295_, v___y_8296_, v___y_8297_, v___x_8321_);
return v___x_8323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_traceArgs_8337_, lean_object* v_weakArgs_8338_, lean_object* v_libName_8339_, lean_object* v_libFile_8340_, lean_object* v_objs_8341_, lean_object* v_plugin_8342_, lean_object* v_linkDeps_8343_, lean_object* v_macosxDeploymentTarget_x3f_8344_, lean_object* v_libs_8345_, lean_object* v___y_8346_, lean_object* v___y_8347_, lean_object* v___y_8348_, lean_object* v___y_8349_, lean_object* v___y_8350_, lean_object* v___y_8351_, lean_object* v___y_8352_){
_start:
{
uint8_t v_plugin_boxed_8353_; uint8_t v_linkDeps_boxed_8354_; lean_object* v_res_8355_; 
v_plugin_boxed_8353_ = lean_unbox(v_plugin_8342_);
v_linkDeps_boxed_8354_ = lean_unbox(v_linkDeps_8343_);
v_res_8355_ = l_Lake_buildLeanSharedLib___lam__0(v_traceArgs_8337_, v_weakArgs_8338_, v_libName_8339_, v_libFile_8340_, v_objs_8341_, v_plugin_boxed_8353_, v_linkDeps_boxed_8354_, v_macosxDeploymentTarget_x3f_8344_, v_libs_8345_, v___y_8346_, v___y_8347_, v___y_8348_, v___y_8349_, v___y_8350_, v___y_8351_);
lean_dec_ref(v___y_8350_);
lean_dec(v___y_8349_);
lean_dec(v___y_8348_);
lean_dec(v___y_8347_);
return v_res_8355_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_traceArgs_8356_, lean_object* v_weakArgs_8357_, lean_object* v_libName_8358_, lean_object* v_libFile_8359_, uint8_t v_plugin_8360_, uint8_t v_linkDeps_8361_, lean_object* v_macosxDeploymentTarget_x3f_8362_, lean_object* v_linkLibs_8363_, lean_object* v___x_8364_, lean_object* v_objs_8365_, lean_object* v___y_8366_, lean_object* v___y_8367_, lean_object* v___y_8368_, lean_object* v___y_8369_, lean_object* v___y_8370_, lean_object* v___y_8371_){
_start:
{
lean_object* v_trace_8373_; lean_object* v___x_8374_; lean_object* v___x_8375_; lean_object* v___f_8376_; lean_object* v___x_8377_; lean_object* v___x_8378_; lean_object* v___x_8379_; uint8_t v___x_8380_; lean_object* v___x_8381_; lean_object* v___x_8382_; 
v_trace_8373_ = lean_ctor_get(v___y_8371_, 1);
v___x_8374_ = lean_box(v_plugin_8360_);
v___x_8375_ = lean_box(v_linkDeps_8361_);
v___f_8376_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 16, 8);
lean_closure_set(v___f_8376_, 0, v_traceArgs_8356_);
lean_closure_set(v___f_8376_, 1, v_weakArgs_8357_);
lean_closure_set(v___f_8376_, 2, v_libName_8358_);
lean_closure_set(v___f_8376_, 3, v_libFile_8359_);
lean_closure_set(v___f_8376_, 4, v_objs_8365_);
lean_closure_set(v___f_8376_, 5, v___x_8374_);
lean_closure_set(v___f_8376_, 6, v___x_8375_);
lean_closure_set(v___f_8376_, 7, v_macosxDeploymentTarget_x3f_8362_);
v___x_8377_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8378_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8363_, v___x_8377_);
v___x_8379_ = lean_unsigned_to_nat(0u);
v___x_8380_ = 0;
v___x_8381_ = l_Lake_Job_mapM___redArg(v___x_8364_, v___x_8378_, v___f_8376_, v___x_8379_, v___x_8380_, v___y_8366_, v___y_8367_, v___y_8368_, v___y_8369_, v___y_8370_, v_trace_8373_);
v___x_8382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8382_, 0, v___x_8381_);
lean_ctor_set(v___x_8382_, 1, v___y_8371_);
return v___x_8382_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_traceArgs_8383_ = _args[0];
lean_object* v_weakArgs_8384_ = _args[1];
lean_object* v_libName_8385_ = _args[2];
lean_object* v_libFile_8386_ = _args[3];
lean_object* v_plugin_8387_ = _args[4];
lean_object* v_linkDeps_8388_ = _args[5];
lean_object* v_macosxDeploymentTarget_x3f_8389_ = _args[6];
lean_object* v_linkLibs_8390_ = _args[7];
lean_object* v___x_8391_ = _args[8];
lean_object* v_objs_8392_ = _args[9];
lean_object* v___y_8393_ = _args[10];
lean_object* v___y_8394_ = _args[11];
lean_object* v___y_8395_ = _args[12];
lean_object* v___y_8396_ = _args[13];
lean_object* v___y_8397_ = _args[14];
lean_object* v___y_8398_ = _args[15];
lean_object* v___y_8399_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8400_; uint8_t v_linkDeps_boxed_8401_; lean_object* v_res_8402_; 
v_plugin_boxed_8400_ = lean_unbox(v_plugin_8387_);
v_linkDeps_boxed_8401_ = lean_unbox(v_linkDeps_8388_);
v_res_8402_ = l_Lake_buildLeanSharedLib___lam__1(v_traceArgs_8383_, v_weakArgs_8384_, v_libName_8385_, v_libFile_8386_, v_plugin_boxed_8400_, v_linkDeps_boxed_8401_, v_macosxDeploymentTarget_x3f_8389_, v_linkLibs_8390_, v___x_8391_, v_objs_8392_, v___y_8393_, v___y_8394_, v___y_8395_, v___y_8396_, v___y_8397_, v___y_8398_);
lean_dec_ref(v___y_8397_);
lean_dec(v___y_8396_);
lean_dec(v___y_8395_);
lean_dec(v___y_8394_);
lean_dec_ref(v_linkLibs_8390_);
return v_res_8402_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8403_, lean_object* v_libFile_8404_, lean_object* v_linkObjs_8405_, lean_object* v_linkLibs_8406_, lean_object* v_weakArgs_8407_, lean_object* v_traceArgs_8408_, uint8_t v_plugin_8409_, uint8_t v_linkDeps_8410_, lean_object* v_macosxDeploymentTarget_x3f_8411_, lean_object* v_a_8412_, lean_object* v_a_8413_, lean_object* v_a_8414_, lean_object* v_a_8415_, lean_object* v_a_8416_, lean_object* v_a_8417_){
_start:
{
lean_object* v___x_8419_; lean_object* v___x_8420_; lean_object* v___x_8421_; lean_object* v___f_8422_; lean_object* v___x_8423_; lean_object* v___x_8424_; lean_object* v___x_8425_; uint8_t v___x_8426_; lean_object* v___x_8427_; 
v___x_8419_ = l_Lake_instDataKindDynlib;
v___x_8420_ = lean_box(v_plugin_8409_);
v___x_8421_ = lean_box(v_linkDeps_8410_);
v___f_8422_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 17, 9);
lean_closure_set(v___f_8422_, 0, v_traceArgs_8408_);
lean_closure_set(v___f_8422_, 1, v_weakArgs_8407_);
lean_closure_set(v___f_8422_, 2, v_libName_8403_);
lean_closure_set(v___f_8422_, 3, v_libFile_8404_);
lean_closure_set(v___f_8422_, 4, v___x_8420_);
lean_closure_set(v___f_8422_, 5, v___x_8421_);
lean_closure_set(v___f_8422_, 6, v_macosxDeploymentTarget_x3f_8411_);
lean_closure_set(v___f_8422_, 7, v_linkLibs_8406_);
lean_closure_set(v___f_8422_, 8, v___x_8419_);
v___x_8423_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8424_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8405_, v___x_8423_);
v___x_8425_ = lean_unsigned_to_nat(0u);
v___x_8426_ = 1;
v___x_8427_ = l_Lake_Job_bindM___redArg(v___x_8419_, v___x_8424_, v___f_8422_, v___x_8425_, v___x_8426_, v_a_8412_, v_a_8413_, v_a_8414_, v_a_8415_, v_a_8416_, v_a_8417_);
return v___x_8427_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8428_, lean_object* v_libFile_8429_, lean_object* v_linkObjs_8430_, lean_object* v_linkLibs_8431_, lean_object* v_weakArgs_8432_, lean_object* v_traceArgs_8433_, lean_object* v_plugin_8434_, lean_object* v_linkDeps_8435_, lean_object* v_macosxDeploymentTarget_x3f_8436_, lean_object* v_a_8437_, lean_object* v_a_8438_, lean_object* v_a_8439_, lean_object* v_a_8440_, lean_object* v_a_8441_, lean_object* v_a_8442_, lean_object* v_a_8443_){
_start:
{
uint8_t v_plugin_boxed_8444_; uint8_t v_linkDeps_boxed_8445_; lean_object* v_res_8446_; 
v_plugin_boxed_8444_ = lean_unbox(v_plugin_8434_);
v_linkDeps_boxed_8445_ = lean_unbox(v_linkDeps_8435_);
v_res_8446_ = l_Lake_buildLeanSharedLib(v_libName_8428_, v_libFile_8429_, v_linkObjs_8430_, v_linkLibs_8431_, v_weakArgs_8432_, v_traceArgs_8433_, v_plugin_boxed_8444_, v_linkDeps_boxed_8445_, v_macosxDeploymentTarget_x3f_8436_, v_a_8437_, v_a_8438_, v_a_8439_, v_a_8440_, v_a_8441_, v_a_8442_);
lean_dec_ref(v_a_8442_);
lean_dec_ref(v_a_8441_);
lean_dec(v_a_8440_);
lean_dec(v_a_8439_);
lean_dec(v_a_8438_);
lean_dec_ref(v_linkObjs_8430_);
return v_res_8446_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object* v_linkLibs_8447_, lean_object* v_linkObjs_8448_, lean_object* v_args_8449_, uint8_t v_sharedLean_8450_, lean_object* v_exeFile_8451_, lean_object* v___y_8452_, lean_object* v___y_8453_, lean_object* v___y_8454_, lean_object* v___y_8455_, lean_object* v___y_8456_, lean_object* v___y_8457_, lean_object* v___y_8458_){
_start:
{
lean_object* v___x_8460_; 
v___x_8460_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8447_, v___y_8458_);
if (lean_obj_tag(v___x_8460_) == 0)
{
lean_object* v_toContext_8461_; lean_object* v_lakeEnv_8462_; lean_object* v_lean_8463_; lean_object* v_a_8464_; lean_object* v_a_8465_; lean_object* v_leanLibDir_8466_; lean_object* v_cc_8467_; lean_object* v_log_8468_; uint8_t v_action_8469_; uint8_t v_wantsRebuild_8470_; lean_object* v_trace_8471_; lean_object* v_buildTime_8472_; lean_object* v___x_8474_; uint8_t v_isShared_8475_; uint8_t v_isSharedCheck_8510_; 
v_toContext_8461_ = lean_ctor_get(v___y_8457_, 1);
v_lakeEnv_8462_ = lean_ctor_get(v_toContext_8461_, 0);
v_lean_8463_ = lean_ctor_get(v_lakeEnv_8462_, 1);
v_a_8464_ = lean_ctor_get(v___x_8460_, 1);
lean_inc(v_a_8464_);
v_a_8465_ = lean_ctor_get(v___x_8460_, 0);
lean_inc(v_a_8465_);
lean_dec_ref_known(v___x_8460_, 2);
v_leanLibDir_8466_ = lean_ctor_get(v_lean_8463_, 3);
v_cc_8467_ = lean_ctor_get(v_lean_8463_, 14);
v_log_8468_ = lean_ctor_get(v_a_8464_, 0);
v_action_8469_ = lean_ctor_get_uint8(v_a_8464_, sizeof(void*)*3);
v_wantsRebuild_8470_ = lean_ctor_get_uint8(v_a_8464_, sizeof(void*)*3 + 1);
v_trace_8471_ = lean_ctor_get(v_a_8464_, 1);
v_buildTime_8472_ = lean_ctor_get(v_a_8464_, 2);
v_isSharedCheck_8510_ = !lean_is_exclusive(v_a_8464_);
if (v_isSharedCheck_8510_ == 0)
{
v___x_8474_ = v_a_8464_;
v_isShared_8475_ = v_isSharedCheck_8510_;
goto v_resetjp_8473_;
}
else
{
lean_inc(v_buildTime_8472_);
lean_inc(v_trace_8471_);
lean_inc(v_log_8468_);
lean_dec(v_a_8464_);
v___x_8474_ = lean_box(0);
v_isShared_8475_ = v_isSharedCheck_8510_;
goto v_resetjp_8473_;
}
v_resetjp_8473_:
{
lean_object* v___x_8476_; lean_object* v___x_8477_; lean_object* v___x_8478_; lean_object* v___x_8479_; lean_object* v___x_8480_; lean_object* v___x_8481_; lean_object* v___x_8482_; lean_object* v___x_8483_; lean_object* v___x_8484_; lean_object* v___x_8485_; 
v___x_8476_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8448_, v_a_8465_);
lean_dec(v_a_8465_);
v___x_8477_ = l_Array_append___redArg(v___x_8476_, v_args_8449_);
v___x_8478_ = lean_unsigned_to_nat(2u);
v___x_8479_ = lean_mk_empty_array_with_capacity(v___x_8478_);
lean_dec_ref(v___x_8479_);
v___x_8480_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8466_);
v___x_8481_ = lean_array_push(v___x_8480_, v_leanLibDir_8466_);
v___x_8482_ = l_Array_append___redArg(v___x_8477_, v___x_8481_);
lean_dec_ref(v___x_8481_);
v___x_8483_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8450_, v_lean_8463_);
v___x_8484_ = l_Array_append___redArg(v___x_8482_, v___x_8483_);
lean_dec_ref(v___x_8483_);
lean_inc_ref(v_cc_8467_);
v___x_8485_ = l_Lake_compileExe(v_exeFile_8451_, v___x_8484_, v_cc_8467_, v___y_8452_, v_log_8468_);
lean_dec_ref(v___x_8484_);
if (lean_obj_tag(v___x_8485_) == 0)
{
lean_object* v_a_8486_; lean_object* v_a_8487_; lean_object* v___x_8489_; uint8_t v_isShared_8490_; uint8_t v_isSharedCheck_8497_; 
v_a_8486_ = lean_ctor_get(v___x_8485_, 0);
v_a_8487_ = lean_ctor_get(v___x_8485_, 1);
v_isSharedCheck_8497_ = !lean_is_exclusive(v___x_8485_);
if (v_isSharedCheck_8497_ == 0)
{
v___x_8489_ = v___x_8485_;
v_isShared_8490_ = v_isSharedCheck_8497_;
goto v_resetjp_8488_;
}
else
{
lean_inc(v_a_8487_);
lean_inc(v_a_8486_);
lean_dec(v___x_8485_);
v___x_8489_ = lean_box(0);
v_isShared_8490_ = v_isSharedCheck_8497_;
goto v_resetjp_8488_;
}
v_resetjp_8488_:
{
lean_object* v___x_8492_; 
if (v_isShared_8475_ == 0)
{
lean_ctor_set(v___x_8474_, 0, v_a_8487_);
v___x_8492_ = v___x_8474_;
goto v_reusejp_8491_;
}
else
{
lean_object* v_reuseFailAlloc_8496_; 
v_reuseFailAlloc_8496_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8496_, 0, v_a_8487_);
lean_ctor_set(v_reuseFailAlloc_8496_, 1, v_trace_8471_);
lean_ctor_set(v_reuseFailAlloc_8496_, 2, v_buildTime_8472_);
lean_ctor_set_uint8(v_reuseFailAlloc_8496_, sizeof(void*)*3, v_action_8469_);
lean_ctor_set_uint8(v_reuseFailAlloc_8496_, sizeof(void*)*3 + 1, v_wantsRebuild_8470_);
v___x_8492_ = v_reuseFailAlloc_8496_;
goto v_reusejp_8491_;
}
v_reusejp_8491_:
{
lean_object* v___x_8494_; 
if (v_isShared_8490_ == 0)
{
lean_ctor_set(v___x_8489_, 1, v___x_8492_);
v___x_8494_ = v___x_8489_;
goto v_reusejp_8493_;
}
else
{
lean_object* v_reuseFailAlloc_8495_; 
v_reuseFailAlloc_8495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8495_, 0, v_a_8486_);
lean_ctor_set(v_reuseFailAlloc_8495_, 1, v___x_8492_);
v___x_8494_ = v_reuseFailAlloc_8495_;
goto v_reusejp_8493_;
}
v_reusejp_8493_:
{
return v___x_8494_;
}
}
}
}
else
{
lean_object* v_a_8498_; lean_object* v_a_8499_; lean_object* v___x_8501_; uint8_t v_isShared_8502_; uint8_t v_isSharedCheck_8509_; 
v_a_8498_ = lean_ctor_get(v___x_8485_, 0);
v_a_8499_ = lean_ctor_get(v___x_8485_, 1);
v_isSharedCheck_8509_ = !lean_is_exclusive(v___x_8485_);
if (v_isSharedCheck_8509_ == 0)
{
v___x_8501_ = v___x_8485_;
v_isShared_8502_ = v_isSharedCheck_8509_;
goto v_resetjp_8500_;
}
else
{
lean_inc(v_a_8499_);
lean_inc(v_a_8498_);
lean_dec(v___x_8485_);
v___x_8501_ = lean_box(0);
v_isShared_8502_ = v_isSharedCheck_8509_;
goto v_resetjp_8500_;
}
v_resetjp_8500_:
{
lean_object* v___x_8504_; 
if (v_isShared_8475_ == 0)
{
lean_ctor_set(v___x_8474_, 0, v_a_8499_);
v___x_8504_ = v___x_8474_;
goto v_reusejp_8503_;
}
else
{
lean_object* v_reuseFailAlloc_8508_; 
v_reuseFailAlloc_8508_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8508_, 0, v_a_8499_);
lean_ctor_set(v_reuseFailAlloc_8508_, 1, v_trace_8471_);
lean_ctor_set(v_reuseFailAlloc_8508_, 2, v_buildTime_8472_);
lean_ctor_set_uint8(v_reuseFailAlloc_8508_, sizeof(void*)*3, v_action_8469_);
lean_ctor_set_uint8(v_reuseFailAlloc_8508_, sizeof(void*)*3 + 1, v_wantsRebuild_8470_);
v___x_8504_ = v_reuseFailAlloc_8508_;
goto v_reusejp_8503_;
}
v_reusejp_8503_:
{
lean_object* v___x_8506_; 
if (v_isShared_8502_ == 0)
{
lean_ctor_set(v___x_8501_, 1, v___x_8504_);
v___x_8506_ = v___x_8501_;
goto v_reusejp_8505_;
}
else
{
lean_object* v_reuseFailAlloc_8507_; 
v_reuseFailAlloc_8507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8507_, 0, v_a_8498_);
lean_ctor_set(v_reuseFailAlloc_8507_, 1, v___x_8504_);
v___x_8506_ = v_reuseFailAlloc_8507_;
goto v_reusejp_8505_;
}
v_reusejp_8505_:
{
return v___x_8506_;
}
}
}
}
}
}
else
{
lean_object* v_a_8511_; lean_object* v_a_8512_; lean_object* v___x_8514_; uint8_t v_isShared_8515_; uint8_t v_isSharedCheck_8519_; 
lean_dec(v___y_8452_);
lean_dec_ref(v_exeFile_8451_);
v_a_8511_ = lean_ctor_get(v___x_8460_, 0);
v_a_8512_ = lean_ctor_get(v___x_8460_, 1);
v_isSharedCheck_8519_ = !lean_is_exclusive(v___x_8460_);
if (v_isSharedCheck_8519_ == 0)
{
v___x_8514_ = v___x_8460_;
v_isShared_8515_ = v_isSharedCheck_8519_;
goto v_resetjp_8513_;
}
else
{
lean_inc(v_a_8512_);
lean_inc(v_a_8511_);
lean_dec(v___x_8460_);
v___x_8514_ = lean_box(0);
v_isShared_8515_ = v_isSharedCheck_8519_;
goto v_resetjp_8513_;
}
v_resetjp_8513_:
{
lean_object* v___x_8517_; 
if (v_isShared_8515_ == 0)
{
v___x_8517_ = v___x_8514_;
goto v_reusejp_8516_;
}
else
{
lean_object* v_reuseFailAlloc_8518_; 
v_reuseFailAlloc_8518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8518_, 0, v_a_8511_);
lean_ctor_set(v_reuseFailAlloc_8518_, 1, v_a_8512_);
v___x_8517_ = v_reuseFailAlloc_8518_;
goto v_reusejp_8516_;
}
v_reusejp_8516_:
{
return v___x_8517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object* v_linkLibs_8520_, lean_object* v_linkObjs_8521_, lean_object* v_args_8522_, lean_object* v_sharedLean_8523_, lean_object* v_exeFile_8524_, lean_object* v___y_8525_, lean_object* v___y_8526_, lean_object* v___y_8527_, lean_object* v___y_8528_, lean_object* v___y_8529_, lean_object* v___y_8530_, lean_object* v___y_8531_, lean_object* v___y_8532_){
_start:
{
uint8_t v_sharedLean_boxed_8533_; lean_object* v_res_8534_; 
v_sharedLean_boxed_8533_ = lean_unbox(v_sharedLean_8523_);
v_res_8534_ = l_Lake_buildLeanExeSync___lam__0(v_linkLibs_8520_, v_linkObjs_8521_, v_args_8522_, v_sharedLean_boxed_8533_, v_exeFile_8524_, v___y_8525_, v___y_8526_, v___y_8527_, v___y_8528_, v___y_8529_, v___y_8530_, v___y_8531_);
lean_dec_ref(v___y_8530_);
lean_dec(v___y_8529_);
lean_dec(v___y_8528_);
lean_dec(v___y_8527_);
lean_dec_ref(v___y_8526_);
lean_dec_ref(v_args_8522_);
lean_dec_ref(v_linkObjs_8521_);
lean_dec_ref(v_linkLibs_8520_);
return v_res_8534_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object* v_exeFile_8535_, lean_object* v_linkObjs_8536_, lean_object* v_linkLibs_8537_, lean_object* v_args_8538_, uint8_t v_sharedLean_8539_, lean_object* v_macosxDeploymentTarget_x3f_8540_, lean_object* v_a_8541_, lean_object* v_a_8542_, lean_object* v_a_8543_, lean_object* v_a_8544_, lean_object* v_a_8545_, lean_object* v_a_8546_){
_start:
{
lean_object* v___y_8549_; lean_object* v___y_8550_; lean_object* v___y_8551_; lean_object* v___y_8552_; lean_object* v___y_8553_; lean_object* v___y_8554_; lean_object* v___y_8555_; lean_object* v_log_8579_; uint8_t v_action_8580_; uint8_t v_wantsRebuild_8581_; lean_object* v_trace_8582_; lean_object* v_buildTime_8583_; lean_object* v___x_8585_; uint8_t v_isShared_8586_; uint8_t v_isSharedCheck_8615_; 
v_log_8579_ = lean_ctor_get(v_a_8546_, 0);
v_action_8580_ = lean_ctor_get_uint8(v_a_8546_, sizeof(void*)*3);
v_wantsRebuild_8581_ = lean_ctor_get_uint8(v_a_8546_, sizeof(void*)*3 + 1);
v_trace_8582_ = lean_ctor_get(v_a_8546_, 1);
v_buildTime_8583_ = lean_ctor_get(v_a_8546_, 2);
v_isSharedCheck_8615_ = !lean_is_exclusive(v_a_8546_);
if (v_isSharedCheck_8615_ == 0)
{
v___x_8585_ = v_a_8546_;
v_isShared_8586_ = v_isSharedCheck_8615_;
goto v_resetjp_8584_;
}
else
{
lean_inc(v_buildTime_8583_);
lean_inc(v_trace_8582_);
lean_inc(v_log_8579_);
lean_dec(v_a_8546_);
v___x_8585_ = lean_box(0);
v_isShared_8586_ = v_isSharedCheck_8615_;
goto v_resetjp_8584_;
}
v___jp_8548_:
{
uint8_t v___x_8556_; uint8_t v___x_8557_; lean_object* v___x_8558_; lean_object* v___x_8559_; 
v___x_8556_ = 1;
v___x_8557_ = 0;
v___x_8558_ = l_System_FilePath_exeExtension;
v___x_8559_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8535_, v___y_8549_, v___x_8557_, v___x_8558_, v___x_8556_, v___x_8556_, v___x_8557_, v___y_8550_, v___y_8551_, v___y_8552_, v___y_8553_, v___y_8554_, v___y_8555_);
if (lean_obj_tag(v___x_8559_) == 0)
{
lean_object* v_a_8560_; lean_object* v_a_8561_; lean_object* v___x_8563_; uint8_t v_isShared_8564_; uint8_t v_isSharedCheck_8569_; 
v_a_8560_ = lean_ctor_get(v___x_8559_, 0);
v_a_8561_ = lean_ctor_get(v___x_8559_, 1);
v_isSharedCheck_8569_ = !lean_is_exclusive(v___x_8559_);
if (v_isSharedCheck_8569_ == 0)
{
v___x_8563_ = v___x_8559_;
v_isShared_8564_ = v_isSharedCheck_8569_;
goto v_resetjp_8562_;
}
else
{
lean_inc(v_a_8561_);
lean_inc(v_a_8560_);
lean_dec(v___x_8559_);
v___x_8563_ = lean_box(0);
v_isShared_8564_ = v_isSharedCheck_8569_;
goto v_resetjp_8562_;
}
v_resetjp_8562_:
{
lean_object* v_path_8565_; lean_object* v___x_8567_; 
v_path_8565_ = lean_ctor_get(v_a_8560_, 1);
lean_inc_ref(v_path_8565_);
lean_dec(v_a_8560_);
if (v_isShared_8564_ == 0)
{
lean_ctor_set(v___x_8563_, 0, v_path_8565_);
v___x_8567_ = v___x_8563_;
goto v_reusejp_8566_;
}
else
{
lean_object* v_reuseFailAlloc_8568_; 
v_reuseFailAlloc_8568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8568_, 0, v_path_8565_);
lean_ctor_set(v_reuseFailAlloc_8568_, 1, v_a_8561_);
v___x_8567_ = v_reuseFailAlloc_8568_;
goto v_reusejp_8566_;
}
v_reusejp_8566_:
{
return v___x_8567_;
}
}
}
else
{
lean_object* v_a_8570_; lean_object* v_a_8571_; lean_object* v___x_8573_; uint8_t v_isShared_8574_; uint8_t v_isSharedCheck_8578_; 
v_a_8570_ = lean_ctor_get(v___x_8559_, 0);
v_a_8571_ = lean_ctor_get(v___x_8559_, 1);
v_isSharedCheck_8578_ = !lean_is_exclusive(v___x_8559_);
if (v_isSharedCheck_8578_ == 0)
{
v___x_8573_ = v___x_8559_;
v_isShared_8574_ = v_isSharedCheck_8578_;
goto v_resetjp_8572_;
}
else
{
lean_inc(v_a_8571_);
lean_inc(v_a_8570_);
lean_dec(v___x_8559_);
v___x_8573_ = lean_box(0);
v_isShared_8574_ = v_isSharedCheck_8578_;
goto v_resetjp_8572_;
}
v_resetjp_8572_:
{
lean_object* v___x_8576_; 
if (v_isShared_8574_ == 0)
{
v___x_8576_ = v___x_8573_;
goto v_reusejp_8575_;
}
else
{
lean_object* v_reuseFailAlloc_8577_; 
v_reuseFailAlloc_8577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8577_, 0, v_a_8570_);
lean_ctor_set(v_reuseFailAlloc_8577_, 1, v_a_8571_);
v___x_8576_ = v_reuseFailAlloc_8577_;
goto v_reusejp_8575_;
}
v_reusejp_8575_:
{
return v___x_8576_;
}
}
}
}
v_resetjp_8584_:
{
lean_object* v_toBuildConfig_8587_; lean_object* v_leanTrace_8588_; lean_object* v___x_8589_; lean_object* v___x_8590_; lean_object* v___x_8591_; lean_object* v___x_8593_; 
v_toBuildConfig_8587_ = lean_ctor_get(v_a_8545_, 0);
v_leanTrace_8588_ = lean_ctor_get(v_a_8545_, 2);
lean_inc_ref(v_leanTrace_8588_);
v___x_8589_ = l_Lake_BuildTrace_mix(v_trace_8582_, v_leanTrace_8588_);
v___x_8590_ = l_Lake_platformTrace;
v___x_8591_ = l_Lake_BuildTrace_mix(v___x_8589_, v___x_8590_);
lean_inc(v_buildTime_8583_);
lean_inc_ref(v___x_8591_);
lean_inc_ref(v_log_8579_);
if (v_isShared_8586_ == 0)
{
lean_ctor_set(v___x_8585_, 1, v___x_8591_);
v___x_8593_ = v___x_8585_;
goto v_reusejp_8592_;
}
else
{
lean_object* v_reuseFailAlloc_8614_; 
v_reuseFailAlloc_8614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8614_, 0, v_log_8579_);
lean_ctor_set(v_reuseFailAlloc_8614_, 1, v___x_8591_);
lean_ctor_set(v_reuseFailAlloc_8614_, 2, v_buildTime_8583_);
lean_ctor_set_uint8(v_reuseFailAlloc_8614_, sizeof(void*)*3, v_action_8580_);
lean_ctor_set_uint8(v_reuseFailAlloc_8614_, sizeof(void*)*3 + 1, v_wantsRebuild_8581_);
v___x_8593_ = v_reuseFailAlloc_8614_;
goto v_reusejp_8592_;
}
v_reusejp_8592_:
{
lean_object* v___y_8595_; lean_object* v_val_8596_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8540_) == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_8609_; lean_object* v___x_8610_; lean_object* v___f_8611_; 
v_macosxDeploymentTarget_x3f_8609_ = lean_ctor_get(v_toBuildConfig_8587_, 3);
v___x_8610_ = lean_box(v_sharedLean_8539_);
lean_inc(v_macosxDeploymentTarget_x3f_8609_);
lean_inc_ref(v_exeFile_8535_);
lean_inc_ref(v_args_8538_);
lean_inc_ref(v_linkObjs_8536_);
lean_inc_ref(v_linkLibs_8537_);
v___f_8611_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8611_, 0, v_linkLibs_8537_);
lean_closure_set(v___f_8611_, 1, v_linkObjs_8536_);
lean_closure_set(v___f_8611_, 2, v_args_8538_);
lean_closure_set(v___f_8611_, 3, v___x_8610_);
lean_closure_set(v___f_8611_, 4, v_exeFile_8535_);
lean_closure_set(v___f_8611_, 5, v_macosxDeploymentTarget_x3f_8609_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8609_) == 1)
{
lean_object* v_val_8612_; 
lean_dec_ref(v___f_8611_);
lean_dec_ref(v___x_8593_);
v_val_8612_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8609_, 0);
lean_inc(v_val_8612_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_8609_);
v___y_8595_ = v_macosxDeploymentTarget_x3f_8609_;
v_val_8596_ = v_val_8612_;
goto v___jp_8594_;
}
else
{
lean_dec_ref(v___x_8591_);
lean_dec(v_buildTime_8583_);
lean_dec_ref(v_log_8579_);
lean_dec_ref(v_args_8538_);
lean_dec_ref(v_linkLibs_8537_);
lean_dec_ref(v_linkObjs_8536_);
v___y_8549_ = v___f_8611_;
v___y_8550_ = v_a_8541_;
v___y_8551_ = v_a_8542_;
v___y_8552_ = v_a_8543_;
v___y_8553_ = v_a_8544_;
v___y_8554_ = v_a_8545_;
v___y_8555_ = v___x_8593_;
goto v___jp_8548_;
}
}
else
{
lean_object* v_val_8613_; 
lean_dec_ref(v___x_8593_);
v_val_8613_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8540_, 0);
lean_inc(v_val_8613_);
v___y_8595_ = v_macosxDeploymentTarget_x3f_8540_;
v_val_8596_ = v_val_8613_;
goto v___jp_8594_;
}
v___jp_8594_:
{
lean_object* v___x_8597_; lean_object* v___f_8598_; uint64_t v___x_8599_; uint64_t v___x_8600_; uint64_t v___x_8601_; lean_object* v___x_8602_; lean_object* v___x_8603_; lean_object* v___x_8604_; lean_object* v___x_8605_; lean_object* v___x_8606_; lean_object* v___x_8607_; lean_object* v___x_8608_; 
v___x_8597_ = lean_box(v_sharedLean_8539_);
lean_inc_ref(v_exeFile_8535_);
v___f_8598_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8598_, 0, v_linkLibs_8537_);
lean_closure_set(v___f_8598_, 1, v_linkObjs_8536_);
lean_closure_set(v___f_8598_, 2, v_args_8538_);
lean_closure_set(v___f_8598_, 3, v___x_8597_);
lean_closure_set(v___f_8598_, 4, v_exeFile_8535_);
lean_closure_set(v___f_8598_, 5, v___y_8595_);
v___x_8599_ = l_Lake_Hash_nil;
v___x_8600_ = lean_string_hash(v_val_8596_);
v___x_8601_ = lean_uint64_mix_hash(v___x_8599_, v___x_8600_);
v___x_8602_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_8603_ = lean_string_append(v___x_8602_, v_val_8596_);
lean_dec_ref(v_val_8596_);
v___x_8604_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8605_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8606_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8606_, 0, v___x_8603_);
lean_ctor_set(v___x_8606_, 1, v___x_8604_);
lean_ctor_set(v___x_8606_, 2, v___x_8605_);
lean_ctor_set_uint64(v___x_8606_, sizeof(void*)*3, v___x_8601_);
v___x_8607_ = l_Lake_BuildTrace_mix(v___x_8591_, v___x_8606_);
v___x_8608_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_8608_, 0, v_log_8579_);
lean_ctor_set(v___x_8608_, 1, v___x_8607_);
lean_ctor_set(v___x_8608_, 2, v_buildTime_8583_);
lean_ctor_set_uint8(v___x_8608_, sizeof(void*)*3, v_action_8580_);
lean_ctor_set_uint8(v___x_8608_, sizeof(void*)*3 + 1, v_wantsRebuild_8581_);
v___y_8549_ = v___f_8598_;
v___y_8550_ = v_a_8541_;
v___y_8551_ = v_a_8542_;
v___y_8552_ = v_a_8543_;
v___y_8553_ = v_a_8544_;
v___y_8554_ = v_a_8545_;
v___y_8555_ = v___x_8608_;
goto v___jp_8548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object* v_exeFile_8616_, lean_object* v_linkObjs_8617_, lean_object* v_linkLibs_8618_, lean_object* v_args_8619_, lean_object* v_sharedLean_8620_, lean_object* v_macosxDeploymentTarget_x3f_8621_, lean_object* v_a_8622_, lean_object* v_a_8623_, lean_object* v_a_8624_, lean_object* v_a_8625_, lean_object* v_a_8626_, lean_object* v_a_8627_, lean_object* v_a_8628_){
_start:
{
uint8_t v_sharedLean_boxed_8629_; lean_object* v_res_8630_; 
v_sharedLean_boxed_8629_ = lean_unbox(v_sharedLean_8620_);
v_res_8630_ = l_Lake_buildLeanExeSync(v_exeFile_8616_, v_linkObjs_8617_, v_linkLibs_8618_, v_args_8619_, v_sharedLean_boxed_8629_, v_macosxDeploymentTarget_x3f_8621_, v_a_8622_, v_a_8623_, v_a_8624_, v_a_8625_, v_a_8626_, v_a_8627_);
lean_dec_ref(v_a_8626_);
lean_dec(v_a_8625_);
lean_dec(v_a_8624_);
lean_dec(v_a_8623_);
return v_res_8630_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_traceArgs_8631_, lean_object* v_weakArgs_8632_, lean_object* v_exeFile_8633_, lean_object* v_objs_8634_, uint8_t v_sharedLean_8635_, lean_object* v_macosxDeploymentTarget_x3f_8636_, lean_object* v_libs_8637_, lean_object* v___y_8638_, lean_object* v___y_8639_, lean_object* v___y_8640_, lean_object* v___y_8641_, lean_object* v___y_8642_, lean_object* v___y_8643_){
_start:
{
uint64_t v___y_8646_; uint64_t v___x_8671_; lean_object* v___x_8672_; lean_object* v___x_8673_; uint8_t v___x_8674_; 
v___x_8671_ = l_Lake_Hash_nil;
v___x_8672_ = lean_unsigned_to_nat(0u);
v___x_8673_ = lean_array_get_size(v_traceArgs_8631_);
v___x_8674_ = lean_nat_dec_lt(v___x_8672_, v___x_8673_);
if (v___x_8674_ == 0)
{
v___y_8646_ = v___x_8671_;
goto v___jp_8645_;
}
else
{
uint8_t v___x_8675_; 
v___x_8675_ = lean_nat_dec_le(v___x_8673_, v___x_8673_);
if (v___x_8675_ == 0)
{
if (v___x_8674_ == 0)
{
v___y_8646_ = v___x_8671_;
goto v___jp_8645_;
}
else
{
size_t v___x_8676_; size_t v___x_8677_; uint64_t v___x_8678_; 
v___x_8676_ = ((size_t)0ULL);
v___x_8677_ = lean_usize_of_nat(v___x_8673_);
v___x_8678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8631_, v___x_8676_, v___x_8677_, v___x_8671_);
v___y_8646_ = v___x_8678_;
goto v___jp_8645_;
}
}
else
{
size_t v___x_8679_; size_t v___x_8680_; uint64_t v___x_8681_; 
v___x_8679_ = ((size_t)0ULL);
v___x_8680_ = lean_usize_of_nat(v___x_8673_);
v___x_8681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8631_, v___x_8679_, v___x_8680_, v___x_8671_);
v___y_8646_ = v___x_8681_;
goto v___jp_8645_;
}
}
v___jp_8645_:
{
lean_object* v_log_8647_; uint8_t v_action_8648_; uint8_t v_wantsRebuild_8649_; lean_object* v_trace_8650_; lean_object* v_buildTime_8651_; lean_object* v___x_8653_; uint8_t v_isShared_8654_; uint8_t v_isSharedCheck_8670_; 
v_log_8647_ = lean_ctor_get(v___y_8643_, 0);
v_action_8648_ = lean_ctor_get_uint8(v___y_8643_, sizeof(void*)*3);
v_wantsRebuild_8649_ = lean_ctor_get_uint8(v___y_8643_, sizeof(void*)*3 + 1);
v_trace_8650_ = lean_ctor_get(v___y_8643_, 1);
v_buildTime_8651_ = lean_ctor_get(v___y_8643_, 2);
v_isSharedCheck_8670_ = !lean_is_exclusive(v___y_8643_);
if (v_isSharedCheck_8670_ == 0)
{
v___x_8653_ = v___y_8643_;
v_isShared_8654_ = v_isSharedCheck_8670_;
goto v_resetjp_8652_;
}
else
{
lean_inc(v_buildTime_8651_);
lean_inc(v_trace_8650_);
lean_inc(v_log_8647_);
lean_dec(v___y_8643_);
v___x_8653_ = lean_box(0);
v_isShared_8654_ = v_isSharedCheck_8670_;
goto v_resetjp_8652_;
}
v_resetjp_8652_:
{
lean_object* v___x_8655_; lean_object* v___x_8656_; lean_object* v___x_8657_; lean_object* v___x_8658_; lean_object* v___x_8659_; lean_object* v___x_8660_; lean_object* v___x_8661_; lean_object* v___x_8662_; lean_object* v___x_8663_; lean_object* v___x_8664_; lean_object* v___x_8666_; 
v___x_8655_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8656_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8657_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8631_);
v___x_8658_ = lean_array_to_list(v_traceArgs_8631_);
v___x_8659_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8658_);
lean_dec(v___x_8658_);
v___x_8660_ = lean_string_append(v___x_8657_, v___x_8659_);
lean_dec_ref(v___x_8659_);
v___x_8661_ = lean_string_append(v___x_8656_, v___x_8660_);
lean_dec_ref(v___x_8660_);
v___x_8662_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8663_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8663_, 0, v___x_8661_);
lean_ctor_set(v___x_8663_, 1, v___x_8655_);
lean_ctor_set(v___x_8663_, 2, v___x_8662_);
lean_ctor_set_uint64(v___x_8663_, sizeof(void*)*3, v___y_8646_);
v___x_8664_ = l_Lake_BuildTrace_mix(v_trace_8650_, v___x_8663_);
if (v_isShared_8654_ == 0)
{
lean_ctor_set(v___x_8653_, 1, v___x_8664_);
v___x_8666_ = v___x_8653_;
goto v_reusejp_8665_;
}
else
{
lean_object* v_reuseFailAlloc_8669_; 
v_reuseFailAlloc_8669_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8669_, 0, v_log_8647_);
lean_ctor_set(v_reuseFailAlloc_8669_, 1, v___x_8664_);
lean_ctor_set(v_reuseFailAlloc_8669_, 2, v_buildTime_8651_);
lean_ctor_set_uint8(v_reuseFailAlloc_8669_, sizeof(void*)*3, v_action_8648_);
lean_ctor_set_uint8(v_reuseFailAlloc_8669_, sizeof(void*)*3 + 1, v_wantsRebuild_8649_);
v___x_8666_ = v_reuseFailAlloc_8669_;
goto v_reusejp_8665_;
}
v_reusejp_8665_:
{
lean_object* v___x_8667_; lean_object* v___x_8668_; 
v___x_8667_ = l_Array_append___redArg(v_weakArgs_8632_, v_traceArgs_8631_);
lean_dec_ref(v_traceArgs_8631_);
v___x_8668_ = l_Lake_buildLeanExeSync(v_exeFile_8633_, v_objs_8634_, v_libs_8637_, v___x_8667_, v_sharedLean_8635_, v_macosxDeploymentTarget_x3f_8636_, v___y_8638_, v___y_8639_, v___y_8640_, v___y_8641_, v___y_8642_, v___x_8666_);
return v___x_8668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_traceArgs_8682_, lean_object* v_weakArgs_8683_, lean_object* v_exeFile_8684_, lean_object* v_objs_8685_, lean_object* v_sharedLean_8686_, lean_object* v_macosxDeploymentTarget_x3f_8687_, lean_object* v_libs_8688_, lean_object* v___y_8689_, lean_object* v___y_8690_, lean_object* v___y_8691_, lean_object* v___y_8692_, lean_object* v___y_8693_, lean_object* v___y_8694_, lean_object* v___y_8695_){
_start:
{
uint8_t v_sharedLean_boxed_8696_; lean_object* v_res_8697_; 
v_sharedLean_boxed_8696_ = lean_unbox(v_sharedLean_8686_);
v_res_8697_ = l_Lake_buildLeanExe___lam__0(v_traceArgs_8682_, v_weakArgs_8683_, v_exeFile_8684_, v_objs_8685_, v_sharedLean_boxed_8696_, v_macosxDeploymentTarget_x3f_8687_, v_libs_8688_, v___y_8689_, v___y_8690_, v___y_8691_, v___y_8692_, v___y_8693_, v___y_8694_);
lean_dec_ref(v___y_8693_);
lean_dec(v___y_8692_);
lean_dec(v___y_8691_);
lean_dec(v___y_8690_);
return v_res_8697_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_traceArgs_8698_, lean_object* v_weakArgs_8699_, lean_object* v_exeFile_8700_, uint8_t v_sharedLean_8701_, lean_object* v_macosxDeploymentTarget_x3f_8702_, lean_object* v_linkLibs_8703_, lean_object* v___x_8704_, lean_object* v_objs_8705_, lean_object* v___y_8706_, lean_object* v___y_8707_, lean_object* v___y_8708_, lean_object* v___y_8709_, lean_object* v___y_8710_, lean_object* v___y_8711_){
_start:
{
lean_object* v_trace_8713_; lean_object* v___x_8714_; lean_object* v___f_8715_; lean_object* v___x_8716_; lean_object* v___x_8717_; lean_object* v___x_8718_; uint8_t v___x_8719_; lean_object* v___x_8720_; lean_object* v___x_8721_; 
v_trace_8713_ = lean_ctor_get(v___y_8711_, 1);
v___x_8714_ = lean_box(v_sharedLean_8701_);
v___f_8715_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 14, 6);
lean_closure_set(v___f_8715_, 0, v_traceArgs_8698_);
lean_closure_set(v___f_8715_, 1, v_weakArgs_8699_);
lean_closure_set(v___f_8715_, 2, v_exeFile_8700_);
lean_closure_set(v___f_8715_, 3, v_objs_8705_);
lean_closure_set(v___f_8715_, 4, v___x_8714_);
lean_closure_set(v___f_8715_, 5, v_macosxDeploymentTarget_x3f_8702_);
v___x_8716_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8717_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8703_, v___x_8716_);
v___x_8718_ = lean_unsigned_to_nat(0u);
v___x_8719_ = 0;
v___x_8720_ = l_Lake_Job_mapM___redArg(v___x_8704_, v___x_8717_, v___f_8715_, v___x_8718_, v___x_8719_, v___y_8706_, v___y_8707_, v___y_8708_, v___y_8709_, v___y_8710_, v_trace_8713_);
v___x_8721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8721_, 0, v___x_8720_);
lean_ctor_set(v___x_8721_, 1, v___y_8711_);
return v___x_8721_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_traceArgs_8722_, lean_object* v_weakArgs_8723_, lean_object* v_exeFile_8724_, lean_object* v_sharedLean_8725_, lean_object* v_macosxDeploymentTarget_x3f_8726_, lean_object* v_linkLibs_8727_, lean_object* v___x_8728_, lean_object* v_objs_8729_, lean_object* v___y_8730_, lean_object* v___y_8731_, lean_object* v___y_8732_, lean_object* v___y_8733_, lean_object* v___y_8734_, lean_object* v___y_8735_, lean_object* v___y_8736_){
_start:
{
uint8_t v_sharedLean_boxed_8737_; lean_object* v_res_8738_; 
v_sharedLean_boxed_8737_ = lean_unbox(v_sharedLean_8725_);
v_res_8738_ = l_Lake_buildLeanExe___lam__1(v_traceArgs_8722_, v_weakArgs_8723_, v_exeFile_8724_, v_sharedLean_boxed_8737_, v_macosxDeploymentTarget_x3f_8726_, v_linkLibs_8727_, v___x_8728_, v_objs_8729_, v___y_8730_, v___y_8731_, v___y_8732_, v___y_8733_, v___y_8734_, v___y_8735_);
lean_dec_ref(v___y_8734_);
lean_dec(v___y_8733_);
lean_dec(v___y_8732_);
lean_dec(v___y_8731_);
lean_dec_ref(v_linkLibs_8727_);
return v_res_8738_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8739_, lean_object* v_linkObjs_8740_, lean_object* v_linkLibs_8741_, lean_object* v_weakArgs_8742_, lean_object* v_traceArgs_8743_, uint8_t v_sharedLean_8744_, lean_object* v_macosxDeploymentTarget_x3f_8745_, lean_object* v_a_8746_, lean_object* v_a_8747_, lean_object* v_a_8748_, lean_object* v_a_8749_, lean_object* v_a_8750_, lean_object* v_a_8751_){
_start:
{
lean_object* v___x_8753_; lean_object* v___x_8754_; lean_object* v___f_8755_; lean_object* v___x_8756_; lean_object* v___x_8757_; lean_object* v___x_8758_; uint8_t v___x_8759_; lean_object* v___x_8760_; 
v___x_8753_ = l_Lake_instDataKindFilePath;
v___x_8754_ = lean_box(v_sharedLean_8744_);
v___f_8755_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 15, 7);
lean_closure_set(v___f_8755_, 0, v_traceArgs_8743_);
lean_closure_set(v___f_8755_, 1, v_weakArgs_8742_);
lean_closure_set(v___f_8755_, 2, v_exeFile_8739_);
lean_closure_set(v___f_8755_, 3, v___x_8754_);
lean_closure_set(v___f_8755_, 4, v_macosxDeploymentTarget_x3f_8745_);
lean_closure_set(v___f_8755_, 5, v_linkLibs_8741_);
lean_closure_set(v___f_8755_, 6, v___x_8753_);
v___x_8756_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8757_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8740_, v___x_8756_);
v___x_8758_ = lean_unsigned_to_nat(0u);
v___x_8759_ = 1;
v___x_8760_ = l_Lake_Job_bindM___redArg(v___x_8753_, v___x_8757_, v___f_8755_, v___x_8758_, v___x_8759_, v_a_8746_, v_a_8747_, v_a_8748_, v_a_8749_, v_a_8750_, v_a_8751_);
return v___x_8760_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8761_, lean_object* v_linkObjs_8762_, lean_object* v_linkLibs_8763_, lean_object* v_weakArgs_8764_, lean_object* v_traceArgs_8765_, lean_object* v_sharedLean_8766_, lean_object* v_macosxDeploymentTarget_x3f_8767_, lean_object* v_a_8768_, lean_object* v_a_8769_, lean_object* v_a_8770_, lean_object* v_a_8771_, lean_object* v_a_8772_, lean_object* v_a_8773_, lean_object* v_a_8774_){
_start:
{
uint8_t v_sharedLean_boxed_8775_; lean_object* v_res_8776_; 
v_sharedLean_boxed_8775_ = lean_unbox(v_sharedLean_8766_);
v_res_8776_ = l_Lake_buildLeanExe(v_exeFile_8761_, v_linkObjs_8762_, v_linkLibs_8763_, v_weakArgs_8764_, v_traceArgs_8765_, v_sharedLean_boxed_8775_, v_macosxDeploymentTarget_x3f_8767_, v_a_8768_, v_a_8769_, v_a_8770_, v_a_8771_, v_a_8772_, v_a_8773_);
lean_dec_ref(v_a_8773_);
lean_dec_ref(v_a_8772_);
lean_dec(v_a_8771_);
lean_dec(v_a_8770_);
lean_dec(v_a_8769_);
lean_dec_ref(v_linkObjs_8762_);
return v_res_8776_;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadWorkspaceJobM = _init_l_Lake_instMonadWorkspaceJobM();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_buildO___lam__2___boxed__const__1 = _init_l_Lake_buildO___lam__2___boxed__const__1();
lean_mark_persistent(l_Lake_buildO___lam__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Common(builtin);
}
#ifdef __cplusplus
}
#endif
