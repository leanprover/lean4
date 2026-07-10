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
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_Lake_writeBinFileIfNew(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object*);
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
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value;
static const lean_closure_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint64_t v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; uint64_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_667_; uint64_t v___y_668_; lean_object* v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; lean_object* v___y_698_; uint64_t v___y_699_; lean_object* v___y_702_; uint64_t v___y_703_; lean_object* v_a_704_; lean_object* v___y_730_; uint64_t v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
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
lean_ctor_set(v___x_658_, 0, v___y_653_);
lean_ctor_set(v___x_658_, 1, v___y_655_);
lean_ctor_set(v___x_658_, 2, v___y_654_);
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
v___y_654_ = v___y_664_;
v___y_655_ = v___y_663_;
v___y_656_ = v___y_662_;
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
v___y_663_ = v___y_669_;
v___y_664_ = v_a_670_;
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
lean_dec(v___y_669_);
lean_dec_ref(v___y_667_);
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
lean_dec(v___y_669_);
lean_dec_ref(v___y_667_);
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
v___y_663_ = v___y_669_;
v___y_664_ = v_a_670_;
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
v___y_654_ = v_a_670_;
v___y_655_ = v___y_669_;
v___y_656_ = v___y_668_;
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
v___y_668_ = v___y_699_;
v___y_669_ = v___y_698_;
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
v___y_697_ = v___y_702_;
v___y_698_ = v_a_704_;
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
v___y_697_ = v___y_702_;
v___y_698_ = v_a_704_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_a_727_, 1);
v___y_667_ = v___y_702_;
v___y_668_ = v___y_703_;
v___y_669_ = v_a_704_;
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t v_x_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lake_OutputStatus_ctorIdx(v_x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* v_x_1170_){
_start:
{
uint8_t v_x_4__boxed_1171_; lean_object* v_res_1172_; 
v_x_4__boxed_1171_ = lean_unbox(v_x_1170_);
v_res_1172_ = l_Lake_OutputStatus_toCtorIdx(v_x_4__boxed_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1173_){
_start:
{
lean_inc(v_k_1173_);
return v_k_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1174_);
lean_dec(v_k_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1176_, lean_object* v_ctorIdx_1177_, uint8_t v_t_1178_, lean_object* v_h_1179_, lean_object* v_k_1180_){
_start:
{
lean_inc(v_k_1180_);
return v_k_1180_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1181_, lean_object* v_ctorIdx_1182_, lean_object* v_t_1183_, lean_object* v_h_1184_, lean_object* v_k_1185_){
_start:
{
uint8_t v_t_boxed_1186_; lean_object* v_res_1187_; 
v_t_boxed_1186_ = lean_unbox(v_t_1183_);
v_res_1187_ = l_Lake_OutputStatus_ctorElim(v_motive_1181_, v_ctorIdx_1182_, v_t_boxed_1186_, v_h_1184_, v_k_1185_);
lean_dec(v_k_1185_);
lean_dec(v_ctorIdx_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1188_){
_start:
{
lean_inc(v_outOfDate_1188_);
return v_outOfDate_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1189_);
lean_dec(v_outOfDate_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1191_, uint8_t v_t_1192_, lean_object* v_h_1193_, lean_object* v_outOfDate_1194_){
_start:
{
lean_inc(v_outOfDate_1194_);
return v_outOfDate_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1195_, lean_object* v_t_1196_, lean_object* v_h_1197_, lean_object* v_outOfDate_1198_){
_start:
{
uint8_t v_t_boxed_1199_; lean_object* v_res_1200_; 
v_t_boxed_1199_ = lean_unbox(v_t_1196_);
v_res_1200_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1195_, v_t_boxed_1199_, v_h_1197_, v_outOfDate_1198_);
lean_dec(v_outOfDate_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1201_){
_start:
{
lean_inc(v_mtimeUpToDate_1201_);
return v_mtimeUpToDate_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1202_);
lean_dec(v_mtimeUpToDate_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1204_, uint8_t v_t_1205_, lean_object* v_h_1206_, lean_object* v_mtimeUpToDate_1207_){
_start:
{
lean_inc(v_mtimeUpToDate_1207_);
return v_mtimeUpToDate_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1208_, lean_object* v_t_1209_, lean_object* v_h_1210_, lean_object* v_mtimeUpToDate_1211_){
_start:
{
uint8_t v_t_boxed_1212_; lean_object* v_res_1213_; 
v_t_boxed_1212_ = lean_unbox(v_t_1209_);
v_res_1213_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1208_, v_t_boxed_1212_, v_h_1210_, v_mtimeUpToDate_1211_);
lean_dec(v_mtimeUpToDate_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1214_){
_start:
{
lean_inc(v_hashUpToDate_1214_);
return v_hashUpToDate_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1215_);
lean_dec(v_hashUpToDate_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1217_, uint8_t v_t_1218_, lean_object* v_h_1219_, lean_object* v_hashUpToDate_1220_){
_start:
{
lean_inc(v_hashUpToDate_1220_);
return v_hashUpToDate_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1221_, lean_object* v_t_1222_, lean_object* v_h_1223_, lean_object* v_hashUpToDate_1224_){
_start:
{
uint8_t v_t_boxed_1225_; lean_object* v_res_1226_; 
v_t_boxed_1225_ = lean_unbox(v_t_1222_);
v_res_1226_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1221_, v_t_boxed_1225_, v_h_1223_, v_hashUpToDate_1224_);
lean_dec(v_hashUpToDate_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_nat_dec_le(v_n_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_dec_le(v_n_1227_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 2;
return v___x_1232_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 1;
return v___x_1233_;
}
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Lake_OutputStatus_ofNat(v_n_1235_);
lean_dec(v_n_1235_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1238_, uint8_t v_y_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lake_OutputStatus_ctorIdx(v_x_1238_);
v___x_1241_ = l_Lake_OutputStatus_ctorIdx(v_y_1239_);
v___x_1242_ = lean_nat_dec_eq(v___x_1240_, v___x_1241_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1243_, lean_object* v_y_1244_){
_start:
{
uint8_t v_x_13__boxed_1245_; uint8_t v_y_14__boxed_1246_; uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_x_13__boxed_1245_ = lean_unbox(v_x_1243_);
v_y_14__boxed_1246_ = lean_unbox(v_y_1244_);
v_res_1247_ = l_Lake_instDecidableEqOutputStatus(v_x_13__boxed_1245_, v_y_14__boxed_1246_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1249_){
_start:
{
if (v_upToDate_1249_ == 0)
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 2;
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1252_){
_start:
{
uint8_t v_upToDate_boxed_1253_; uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_upToDate_boxed_1253_ = lean_unbox(v_upToDate_1252_);
v_res_1254_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1256_){
_start:
{
if (v_upToDate_1256_ == 0)
{
uint8_t v___x_1257_; 
v___x_1257_ = 0;
return v___x_1257_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = 1;
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1259_){
_start:
{
uint8_t v_upToDate_boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_upToDate_boxed_1260_ = lean_unbox(v_upToDate_1259_);
v_res_1261_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1260_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1263_){
_start:
{
uint8_t v___x_1264_; uint8_t v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = 0;
v___x_1265_ = l_Lake_instDecidableEqOutputStatus(v_status_1263_, v___x_1264_);
v___x_1266_ = lean_bool_not(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1267_){
_start:
{
uint8_t v_status_boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_status_boxed_1268_ = lean_unbox(v_status_1267_);
v_res_1269_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1268_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1271_){
_start:
{
uint8_t v___x_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = 1;
v___x_1273_ = l_Lake_instDecidableEqOutputStatus(v_status_1271_, v___x_1272_);
v___x_1274_ = lean_bool_not(v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1275_){
_start:
{
uint8_t v_status_boxed_1276_; uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_status_boxed_1276_ = lean_unbox(v_status_1275_);
v_res_1277_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1276_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___f_1280_; 
v___x_1279_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1280_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1280_, 0, v___x_1279_);
return v___f_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_info_1283_, lean_object* v_depTrace_1284_, lean_object* v_depHash_1285_, lean_object* v_oldTrace_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
uint64_t v_hash_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_hash_1290_ = lean_ctor_get_uint64(v_depTrace_1284_, sizeof(void*)*3);
v___f_1291_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1292_ = lean_box_uint64(v_hash_1290_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
v___x_1294_ = l_Option_instBEq_beq___redArg(v___f_1291_, v___x_1293_, v_depHash_1285_);
if (v___x_1294_ == 0)
{
lean_object* v_toBuildConfig_1295_; uint8_t v_oldMode_1296_; 
lean_dec_ref(v_inst_1281_);
v_toBuildConfig_1295_ = lean_ctor_get(v_a_1287_, 0);
v_oldMode_1296_ = lean_ctor_get_uint8(v_toBuildConfig_1295_, sizeof(void*)*3);
if (v_oldMode_1296_ == 0)
{
uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_info_1283_);
lean_dec_ref(v_inst_1282_);
v___x_1297_ = 0;
v___x_1298_ = lean_box(v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_a_1288_);
return v___x_1299_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1282_, v_info_1283_, v_oldTrace_1286_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = 0;
v___x_1302_ = lean_box(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v_a_1288_);
return v___x_1303_;
}
else
{
uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = 1;
v___x_1305_ = lean_box(v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_a_1288_);
return v___x_1306_;
}
}
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
lean_dec_ref(v_inst_1282_);
v___x_1307_ = lean_apply_2(v_inst_1281_, v_info_1283_, lean_box(0));
v___x_1308_ = lean_unbox(v___x_1307_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = 0;
v___x_1310_ = lean_box(v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_1288_);
return v___x_1311_;
}
else
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = 2;
v___x_1313_ = lean_box(v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v_a_1288_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_info_1317_, lean_object* v_depTrace_1318_, lean_object* v_depHash_1319_, lean_object* v_oldTrace_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1315_, v_inst_1316_, v_info_1317_, v_depTrace_1318_, v_depHash_1319_, v_oldTrace_1320_, v_a_1321_, v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec_ref(v_oldTrace_1320_);
lean_dec_ref(v_depTrace_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_info_1328_, lean_object* v_depTrace_1329_, lean_object* v_depHash_1330_, lean_object* v_oldTrace_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1326_, v_inst_1327_, v_info_1328_, v_depTrace_1329_, v_depHash_1330_, v_oldTrace_1331_, v_a_1336_, v_a_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_info_1343_, lean_object* v_depTrace_1344_, lean_object* v_depHash_1345_, lean_object* v_oldTrace_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1340_, v_inst_1341_, v_inst_1342_, v_info_1343_, v_depTrace_1344_, v_depHash_1345_, v_oldTrace_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_oldTrace_1346_);
lean_dec_ref(v_depTrace_1344_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_info_1357_, lean_object* v_depTrace_1358_, lean_object* v_depHash_1359_, lean_object* v_oldTrace_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1378_; 
v___x_1364_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1355_, v_inst_1356_, v_info_1357_, v_depTrace_1358_, v_depHash_1359_, v_oldTrace_1360_, v_a_1361_, v_a_1362_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_a_1366_ = lean_ctor_get(v___x_1364_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1368_ = v___x_1364_;
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; uint8_t v___x_1371_; uint8_t v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1370_ = 0;
v___x_1371_ = lean_unbox(v_a_1365_);
lean_dec(v_a_1365_);
v___x_1372_ = l_Lake_instDecidableEqOutputStatus(v___x_1371_, v___x_1370_);
v___x_1373_ = lean_bool_not(v___x_1372_);
v___x_1374_ = lean_box(v___x_1373_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1374_);
v___x_1376_ = v___x_1368_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_a_1366_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_info_1381_, lean_object* v_depTrace_1382_, lean_object* v_depHash_1383_, lean_object* v_oldTrace_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lake_checkHashUpToDate___redArg(v_inst_1379_, v_inst_1380_, v_info_1381_, v_depTrace_1382_, v_depHash_1383_, v_oldTrace_1384_, v_a_1385_, v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec_ref(v_oldTrace_1384_);
lean_dec_ref(v_depTrace_1382_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_info_1392_, lean_object* v_depTrace_1393_, lean_object* v_depHash_1394_, lean_object* v_oldTrace_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v_a_1404_; lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1417_; 
v___x_1403_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1390_, v_inst_1391_, v_info_1392_, v_depTrace_1393_, v_depHash_1394_, v_oldTrace_1395_, v_a_1400_, v_a_1401_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_a_1405_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1407_ = v___x_1403_;
v_isShared_1408_ = v_isSharedCheck_1417_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1417_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
uint8_t v___x_1409_; uint8_t v___x_1410_; uint8_t v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1409_ = 0;
v___x_1410_ = lean_unbox(v_a_1404_);
lean_dec(v_a_1404_);
v___x_1411_ = l_Lake_instDecidableEqOutputStatus(v___x_1410_, v___x_1409_);
v___x_1412_ = lean_bool_not(v___x_1411_);
v___x_1413_ = lean_box(v___x_1412_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1413_);
v___x_1415_ = v___x_1407_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1405_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_info_1421_, lean_object* v_depTrace_1422_, lean_object* v_depHash_1423_, lean_object* v_oldTrace_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lake_checkHashUpToDate(v_00_u03b9_1418_, v_inst_1419_, v_inst_1420_, v_info_1421_, v_depTrace_1422_, v_depHash_1423_, v_oldTrace_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec_ref(v_oldTrace_1424_);
lean_dec_ref(v_depTrace_1422_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1439_ == 0)
{
lean_object* v_log_1440_; uint8_t v_action_1441_; uint8_t v_wantsRebuild_1442_; lean_object* v_trace_1443_; lean_object* v_buildTime_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1457_; 
v_log_1440_ = lean_ctor_get(v___y_1437_, 0);
v_action_1441_ = lean_ctor_get_uint8(v___y_1437_, sizeof(void*)*3);
v_wantsRebuild_1442_ = lean_ctor_get_uint8(v___y_1437_, sizeof(void*)*3 + 1);
v_trace_1443_ = lean_ctor_get(v___y_1437_, 1);
v_buildTime_1444_ = lean_ctor_get(v___y_1437_, 2);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___y_1437_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1446_ = v___y_1437_;
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_buildTime_1444_);
lean_inc(v_trace_1443_);
lean_inc(v_log_1440_);
lean_dec(v___y_1437_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1448_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
v___x_1449_ = lean_box(0);
lean_inc(v___x_1448_);
v___x_1450_ = lean_array_push(v_log_1440_, v___x_1448_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1450_);
v___x_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_trace_1443_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_buildTime_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*3, v_action_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*3 + 1, v_wantsRebuild_1442_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
size_t v___x_1453_; size_t v___x_1454_; 
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1434_, v___x_1453_);
v_i_1434_ = v___x_1454_;
v_b_1436_ = v___x_1449_;
v___y_1437_ = v___x_1452_;
goto _start;
}
}
}
else
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_b_1436_);
lean_ctor_set(v___x_1458_, 1, v___y_1437_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1459_, lean_object* v_i_1460_, lean_object* v_stop_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
size_t v_i_boxed_1465_; size_t v_stop_boxed_1466_; lean_object* v_res_1467_; 
v_i_boxed_1465_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_stop_boxed_1466_ = lean_unbox_usize(v_stop_1461_);
lean_dec(v_stop_1461_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1459_, v_i_boxed_1465_, v_stop_boxed_1466_, v_b_1462_, v___y_1463_);
lean_dec_ref(v_as_1459_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_log_1468_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v_a_1474_);
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_nat_dec_le(v___x_1477_, v___x_1477_);
if (v___x_1481_ == 0)
{
if (v___x_1479_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1478_);
lean_ctor_set(v___x_1482_, 1, v_a_1474_);
return v___x_1482_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1477_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1468_, v___x_1483_, v___x_1484_, v___x_1478_, v_a_1474_);
return v___x_1485_;
}
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1477_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1468_, v___x_1486_, v___x_1487_, v___x_1478_, v_a_1474_);
return v___x_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec_ref(v_log_1489_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1498_, size_t v_i_1499_, size_t v_stop_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1498_, v_i_1499_, v_stop_1500_, v_b_1501_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1510_, lean_object* v_i_1511_, lean_object* v_stop_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
size_t v_i_boxed_1521_; size_t v_stop_boxed_1522_; lean_object* v_res_1523_; 
v_i_boxed_1521_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_stop_boxed_1522_ = lean_unbox_usize(v_stop_1512_);
lean_dec(v_stop_1512_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1510_, v_i_boxed_1521_, v_stop_boxed_1522_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_as_1510_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_info_1526_, lean_object* v_depTrace_1527_, lean_object* v_savedTrace_1528_, lean_object* v_oldTrace_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
if (lean_obj_tag(v_savedTrace_1528_) == 2)
{
lean_object* v_data_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1588_; 
v_data_1537_ = lean_ctor_get(v_savedTrace_1528_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_savedTrace_1528_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1539_ = v_savedTrace_1528_;
v_isShared_1540_ = v_isSharedCheck_1588_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_data_1537_);
lean_dec(v_savedTrace_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1588_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint64_t v_depHash_1541_; lean_object* v_log_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_depHash_1541_ = lean_ctor_get_uint64(v_data_1537_, sizeof(void*)*3);
v_log_1542_ = lean_ctor_get(v_data_1537_, 2);
lean_inc_ref(v_log_1542_);
lean_dec_ref(v_data_1537_);
v___x_1543_ = lean_box_uint64(v_depHash_1541_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1543_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v_a_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1586_; 
v___x_1546_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1524_, v_inst_1525_, v_info_1526_, v_depTrace_1527_, v___x_1545_, v_oldTrace_1529_, v_a_1534_, v_a_1535_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_a_1548_ = lean_ctor_get(v___x_1546_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1550_ = v___x_1546_;
v_isShared_1551_ = v_isSharedCheck_1586_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1586_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___y_1553_; uint8_t v___x_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1557_ = 0;
v___x_1558_ = lean_unbox(v_a_1547_);
v___x_1559_ = l_Lake_instDecidableEqOutputStatus(v___x_1558_, v___x_1557_);
v___x_1560_ = lean_bool_not(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_dec_ref(v_log_1542_);
v___y_1553_ = v_a_1548_;
goto v___jp_1552_;
}
else
{
lean_object* v_log_1561_; uint8_t v_action_1562_; uint8_t v_wantsRebuild_1563_; lean_object* v_trace_1564_; lean_object* v_buildTime_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1585_; 
v_log_1561_ = lean_ctor_get(v_a_1548_, 0);
v_action_1562_ = lean_ctor_get_uint8(v_a_1548_, sizeof(void*)*3);
v_wantsRebuild_1563_ = lean_ctor_get_uint8(v_a_1548_, sizeof(void*)*3 + 1);
v_trace_1564_ = lean_ctor_get(v_a_1548_, 1);
v_buildTime_1565_ = lean_ctor_get(v_a_1548_, 2);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1567_ = v_a_1548_;
v_isShared_1568_ = v_isSharedCheck_1585_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_buildTime_1565_);
lean_inc(v_trace_1564_);
lean_inc(v_log_1561_);
lean_dec(v_a_1548_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1585_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
uint8_t v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1572_; 
v___x_1569_ = 2;
v___x_1570_ = l_Lake_JobAction_merge(v_action_1562_, v___x_1569_);
if (v_isShared_1568_ == 0)
{
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_log_1561_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_trace_1564_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_buildTime_1565_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*3 + 1, v_wantsRebuild_1563_);
v___x_1572_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*3, v___x_1570_);
v___x_1573_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1542_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v___x_1572_);
lean_dec_ref(v_log_1542_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 2);
v___y_1553_ = v_a_1574_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_del_object(v___x_1550_);
lean_dec(v_a_1547_);
v_a_1575_ = lean_ctor_get(v___x_1573_, 0);
v_a_1576_ = lean_ctor_get(v___x_1573_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1573_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v___x_1573_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
v___jp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___y_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1547_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___y_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1589_; uint8_t v_oldMode_1590_; 
lean_dec(v_savedTrace_1528_);
lean_dec_ref(v_inst_1524_);
v_toBuildConfig_1589_ = lean_ctor_get(v_a_1534_, 0);
v_oldMode_1590_ = lean_ctor_get_uint8(v_toBuildConfig_1589_, sizeof(void*)*3);
if (v_oldMode_1590_ == 0)
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec(v_info_1526_);
lean_dec_ref(v_inst_1525_);
v___x_1591_ = 0;
v___x_1592_ = lean_box(v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v_a_1535_);
return v___x_1593_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1525_, v_info_1526_, v_oldTrace_1529_);
if (v___x_1594_ == 0)
{
uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = 0;
v___x_1596_ = lean_box(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v_a_1535_);
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = 1;
v___x_1599_ = lean_box(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_a_1535_);
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_info_1603_, lean_object* v_depTrace_1604_, lean_object* v_savedTrace_1605_, lean_object* v_oldTrace_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1601_, v_inst_1602_, v_info_1603_, v_depTrace_1604_, v_savedTrace_1605_, v_oldTrace_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec_ref(v_oldTrace_1606_);
lean_dec_ref(v_depTrace_1604_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_info_1618_, lean_object* v_depTrace_1619_, lean_object* v_savedTrace_1620_, lean_object* v_oldTrace_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1616_, v_inst_1617_, v_info_1618_, v_depTrace_1619_, v_savedTrace_1620_, v_oldTrace_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_info_1633_, lean_object* v_depTrace_1634_, lean_object* v_savedTrace_1635_, lean_object* v_oldTrace_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1630_, v_inst_1631_, v_inst_1632_, v_info_1633_, v_depTrace_1634_, v_savedTrace_1635_, v_oldTrace_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec_ref(v_oldTrace_1636_);
lean_dec_ref(v_depTrace_1634_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_info_1647_, lean_object* v_depTrace_1648_, lean_object* v_savedTrace_1649_, lean_object* v_oldTrace_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1645_, v_inst_1646_, v_info_1647_, v_depTrace_1648_, v_savedTrace_1649_, v_oldTrace_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1672_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___x_1664_; uint8_t v___x_1665_; uint8_t v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1664_ = 0;
v___x_1665_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
v___x_1666_ = l_Lake_instDecidableEqOutputStatus(v___x_1665_, v___x_1664_);
v___x_1667_ = lean_bool_not(v___x_1666_);
v___x_1668_ = lean_box(v___x_1667_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1668_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1660_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1658_, 0);
v_a_1674_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1658_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_inc(v_a_1673_);
lean_dec(v___x_1658_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1673_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_info_1684_, lean_object* v_depTrace_1685_, lean_object* v_savedTrace_1686_, lean_object* v_oldTrace_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1682_, v_inst_1683_, v_info_1684_, v_depTrace_1685_, v_savedTrace_1686_, v_oldTrace_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec_ref(v_oldTrace_1687_);
lean_dec_ref(v_depTrace_1685_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_info_1699_, lean_object* v_depTrace_1700_, lean_object* v_savedTrace_1701_, lean_object* v_oldTrace_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1697_, v_inst_1698_, v_info_1699_, v_depTrace_1700_, v_savedTrace_1701_, v_oldTrace_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1724_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_a_1712_ = lean_ctor_get(v___x_1710_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1714_ = v___x_1710_;
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint8_t v___x_1716_; uint8_t v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1716_ = 0;
v___x_1717_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
v___x_1718_ = l_Lake_instDecidableEqOutputStatus(v___x_1717_, v___x_1716_);
v___x_1719_ = lean_bool_not(v___x_1718_);
v___x_1720_ = lean_box(v___x_1719_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1720_);
v___x_1722_ = v___x_1714_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_a_1712_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1725_ = lean_ctor_get(v___x_1710_, 0);
v_a_1726_ = lean_ctor_get(v___x_1710_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1710_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_inc(v_a_1725_);
lean_dec(v___x_1710_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_info_1737_, lean_object* v_depTrace_1738_, lean_object* v_savedTrace_1739_, lean_object* v_oldTrace_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1734_, v_inst_1735_, v_inst_1736_, v_info_1737_, v_depTrace_1738_, v_savedTrace_1739_, v_oldTrace_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec_ref(v_oldTrace_1740_);
lean_dec_ref(v_depTrace_1738_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t v_inputHash_1749_, lean_object* v_self_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___y_1754_; 
if (lean_obj_tag(v_self_1750_) == 2)
{
lean_object* v_data_1772_; uint64_t v_depHash_1773_; lean_object* v_log_1774_; uint8_t v_synthetic_1775_; uint8_t v___x_1776_; lean_object* v___y_1778_; lean_object* v___y_1782_; 
v_data_1772_ = lean_ctor_get(v_self_1750_, 0);
v_depHash_1773_ = lean_ctor_get_uint64(v_data_1772_, sizeof(void*)*3);
v_log_1774_ = lean_ctor_get(v_data_1772_, 2);
v_synthetic_1775_ = lean_ctor_get_uint8(v_data_1772_, sizeof(void*)*3 + 8);
v___x_1776_ = lean_uint64_dec_eq(v_depHash_1773_, v_inputHash_1749_);
if (v___x_1776_ == 0)
{
v___y_1754_ = v_a_1751_;
goto v___jp_1753_;
}
else
{
if (v_synthetic_1775_ == 0)
{
goto v___jp_1793_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = lean_array_get_size(v_log_1774_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_nat_dec_eq(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
goto v___jp_1793_;
}
else
{
lean_object* v_log_1822_; uint8_t v_action_1823_; uint8_t v_wantsRebuild_1824_; lean_object* v_trace_1825_; lean_object* v_buildTime_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_log_1822_ = lean_ctor_get(v_a_1751_, 0);
v_action_1823_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*3);
v_wantsRebuild_1824_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*3 + 1);
v_trace_1825_ = lean_ctor_get(v_a_1751_, 1);
v_buildTime_1826_ = lean_ctor_get(v_a_1751_, 2);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v_a_1751_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_buildTime_1826_);
lean_inc(v_trace_1825_);
lean_inc(v_log_1822_);
lean_dec(v_a_1751_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
uint8_t v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = 1;
v___x_1831_ = l_Lake_JobAction_merge(v_action_1823_, v___x_1830_);
if (v_isShared_1829_ == 0)
{
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_log_1822_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_trace_1825_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_buildTime_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*3 + 1, v_wantsRebuild_1824_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*3, v___x_1831_);
v___y_1778_ = v___x_1833_;
goto v___jp_1777_;
}
}
}
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_box(v___x_1776_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v___y_1778_);
return v___x_1780_;
}
v___jp_1781_:
{
if (lean_obj_tag(v___y_1782_) == 0)
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___y_1782_, 1);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___y_1782_, 2);
v___y_1778_ = v_a_1783_;
goto v___jp_1777_;
}
else
{
lean_object* v_a_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1784_ = lean_ctor_get(v___y_1782_, 0);
v_a_1785_ = lean_ctor_get(v___y_1782_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___y_1782_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___y_1782_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_inc(v_a_1784_);
lean_dec(v___y_1782_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1784_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
v___jp_1793_:
{
lean_object* v_log_1794_; uint8_t v_action_1795_; uint8_t v_wantsRebuild_1796_; lean_object* v_trace_1797_; lean_object* v_buildTime_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1818_; 
v_log_1794_ = lean_ctor_get(v_a_1751_, 0);
v_action_1795_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*3);
v_wantsRebuild_1796_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*3 + 1);
v_trace_1797_ = lean_ctor_get(v_a_1751_, 1);
v_buildTime_1798_ = lean_ctor_get(v_a_1751_, 2);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1800_ = v_a_1751_;
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_buildTime_1798_);
lean_inc(v_trace_1797_);
lean_inc(v_log_1794_);
lean_dec(v_a_1751_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = 2;
v___x_1803_ = l_Lake_JobAction_merge(v_action_1795_, v___x_1802_);
if (v_isShared_1801_ == 0)
{
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_log_1794_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_trace_1797_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_buildTime_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3 + 1, v_wantsRebuild_1796_);
v___x_1805_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3, v___x_1803_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_log_1774_);
v___x_1808_ = lean_nat_dec_lt(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
v___y_1778_ = v___x_1805_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_nat_dec_le(v___x_1807_, v___x_1807_);
if (v___x_1810_ == 0)
{
if (v___x_1808_ == 0)
{
v___y_1778_ = v___x_1805_;
goto v___jp_1777_;
}
else
{
size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_of_nat(v___x_1807_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1774_, v___x_1811_, v___x_1812_, v___x_1809_, v___x_1805_);
v___y_1782_ = v___x_1813_;
goto v___jp_1781_;
}
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1807_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1774_, v___x_1814_, v___x_1815_, v___x_1809_, v___x_1805_);
v___y_1782_ = v___x_1816_;
goto v___jp_1781_;
}
}
}
}
}
}
else
{
v___y_1754_ = v_a_1751_;
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v_log_1755_; uint8_t v_action_1756_; uint8_t v_wantsRebuild_1757_; lean_object* v_trace_1758_; lean_object* v_buildTime_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1771_; 
v_log_1755_ = lean_ctor_get(v___y_1754_, 0);
v_action_1756_ = lean_ctor_get_uint8(v___y_1754_, sizeof(void*)*3);
v_wantsRebuild_1757_ = lean_ctor_get_uint8(v___y_1754_, sizeof(void*)*3 + 1);
v_trace_1758_ = lean_ctor_get(v___y_1754_, 1);
v_buildTime_1759_ = lean_ctor_get(v___y_1754_, 2);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___y_1754_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1761_ = v___y_1754_;
v_isShared_1762_ = v_isSharedCheck_1771_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_buildTime_1759_);
lean_inc(v_trace_1758_);
lean_inc(v_log_1755_);
lean_dec(v___y_1754_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1771_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = 1;
v___x_1764_ = l_Lake_JobAction_merge(v_action_1756_, v___x_1763_);
if (v_isShared_1762_ == 0)
{
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_log_1755_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_trace_1758_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_buildTime_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3 + 1, v_wantsRebuild_1757_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3, v___x_1764_);
v___x_1767_ = 0;
v___x_1768_ = lean_box(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1766_);
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object* v_inputHash_1836_, lean_object* v_self_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
uint64_t v_inputHash_boxed_1840_; lean_object* v_res_1841_; 
v_inputHash_boxed_1840_ = lean_unbox_uint64(v_inputHash_1836_);
lean_dec_ref(v_inputHash_1836_);
v_res_1841_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_boxed_1840_, v_self_1837_, v_a_1838_);
lean_dec(v_self_1837_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t v_inputHash_1842_, lean_object* v_self_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1842_, v_self_1843_, v_a_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object* v_inputHash_1852_, lean_object* v_self_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint64_t v_inputHash_boxed_1861_; lean_object* v_res_1862_; 
v_inputHash_boxed_1861_ = lean_unbox_uint64(v_inputHash_1852_);
lean_dec_ref(v_inputHash_1852_);
v_res_1862_ = l_Lake_SavedTrace_replayCachedIfUpToDate(v_inputHash_boxed_1861_, v_self_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_self_1853_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1863_, lean_object* v_self_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1863_, v_self_1864_, v_a_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1868_, lean_object* v_self_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
uint64_t v_inputHash_boxed_1872_; lean_object* v_res_1873_; 
v_inputHash_boxed_1872_ = lean_unbox_uint64(v_inputHash_1868_);
lean_dec_ref(v_inputHash_1868_);
v_res_1873_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1872_, v_self_1869_, v_a_1870_);
lean_dec(v_self_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1874_, lean_object* v_self_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1874_, v_self_1875_, v_a_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1884_, lean_object* v_self_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint64_t v_inputHash_boxed_1893_; lean_object* v_res_1894_; 
v_inputHash_boxed_1893_ = lean_unbox_uint64(v_inputHash_1884_);
lean_dec_ref(v_inputHash_1884_);
v_res_1894_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1893_, v_self_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_self_1885_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_box(0);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1900_){
_start:
{
lean_object* v_descr_1901_; uint64_t v_hash_1902_; lean_object* v_ext_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_descr_1901_ = lean_ctor_get(v_x_1900_, 0);
v_hash_1902_ = lean_ctor_get_uint64(v_descr_1901_, sizeof(void*)*1);
v_ext_1903_ = lean_ctor_get(v_descr_1901_, 0);
v___x_1904_ = lean_string_utf8_byte_size(v_ext_1903_);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_nat_dec_eq(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1907_ = l_Lake_lowerHexUInt64(v_hash_1902_);
v___x_1908_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1909_ = lean_string_append(v___x_1907_, v___x_1908_);
v___x_1910_ = lean_string_append(v___x_1909_, v_ext_1903_);
v___x_1911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = l_Lake_lowerHexUInt64(v_hash_1902_);
v___x_1913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1914_);
lean_dec_ref(v_x_1914_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1918_, lean_object* v_a_x3f_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v_log_1923_; uint8_t v_action_1924_; uint8_t v_wantsRebuild_1925_; lean_object* v_trace_1926_; lean_object* v_buildTime_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1938_; 
v___x_1922_ = lean_io_mono_ms_now();
v_log_1923_ = lean_ctor_get(v___y_1920_, 0);
v_action_1924_ = lean_ctor_get_uint8(v___y_1920_, sizeof(void*)*3);
v_wantsRebuild_1925_ = lean_ctor_get_uint8(v___y_1920_, sizeof(void*)*3 + 1);
v_trace_1926_ = lean_ctor_get(v___y_1920_, 1);
v_buildTime_1927_ = lean_ctor_get(v___y_1920_, 2);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___y_1920_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1929_ = v___y_1920_;
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_buildTime_1927_);
lean_inc(v_trace_1926_);
lean_inc(v_log_1923_);
lean_dec(v___y_1920_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1931_ = lean_nat_sub(v___x_1922_, v_val_1918_);
lean_dec(v___x_1922_);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_nat_add(v_buildTime_1927_, v___x_1931_);
lean_dec(v___x_1931_);
lean_dec(v_buildTime_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 2, v___x_1933_);
v___x_1935_ = v___x_1929_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_log_1923_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_trace_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v___x_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3, v_action_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3 + 1, v_wantsRebuild_1925_);
v___x_1935_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1932_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1939_, lean_object* v_a_x3f_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lake_buildAction___redArg___lam__0(v_val_1939_, v_a_x3f_1940_, v___y_1941_);
lean_dec(v_a_x3f_1940_);
lean_dec(v_val_1939_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1949_, lean_object* v_depTrace_1950_, lean_object* v_traceFile_1951_, lean_object* v_build_1952_, uint8_t v_action_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v_log_1966_; uint8_t v_action_1967_; uint8_t v_wantsRebuild_1968_; lean_object* v_trace_1969_; lean_object* v_buildTime_1970_; lean_object* v_toBuildConfig_1976_; lean_object* v_log_1977_; uint8_t v_action_1978_; uint8_t v_wantsRebuild_1979_; lean_object* v_trace_1980_; lean_object* v_buildTime_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2087_; 
v_toBuildConfig_1976_ = lean_ctor_get(v_a_1958_, 0);
v_log_1977_ = lean_ctor_get(v_a_1959_, 0);
v_action_1978_ = lean_ctor_get_uint8(v_a_1959_, sizeof(void*)*3);
v_wantsRebuild_1979_ = lean_ctor_get_uint8(v_a_1959_, sizeof(void*)*3 + 1);
v_trace_1980_ = lean_ctor_get(v_a_1959_, 1);
v_buildTime_1981_ = lean_ctor_get(v_a_1959_, 2);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_a_1959_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_1983_ = v_a_1959_;
v_isShared_1984_ = v_isSharedCheck_2087_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_buildTime_1981_);
lean_inc(v_trace_1980_);
lean_inc(v_log_1977_);
lean_dec(v_a_1959_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2087_;
goto v_resetjp_1982_;
}
v___jp_1961_:
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_a_1962_);
lean_ctor_set(v___x_1964_, 1, v_a_1963_);
return v___x_1964_;
}
v___jp_1965_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1971_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1972_ = lean_array_get_size(v_log_1966_);
v___x_1973_ = lean_array_push(v_log_1966_, v___x_1971_);
v___x_1974_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_trace_1969_);
lean_ctor_set(v___x_1974_, 2, v_buildTime_1970_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*3, v_action_1967_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*3 + 1, v_wantsRebuild_1968_);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
return v___x_1975_;
}
v_resetjp_1982_:
{
uint8_t v_noBuild_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_noBuild_1985_ = lean_ctor_get_uint8(v_toBuildConfig_1976_, sizeof(void*)*3 + 2);
v___x_1986_ = l_Lake_JobAction_merge(v_action_1978_, v_action_1953_);
v___x_1987_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1951_);
v___x_1988_ = l_System_FilePath_addExtension(v_traceFile_1951_, v___x_1987_);
if (v_noBuild_1985_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1977_);
if (v_isShared_1984_ == 0)
{
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_log_1977_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_trace_1980_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_buildTime_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*3 + 1, v_wantsRebuild_1979_);
v___x_1991_ = v_reuseFailAlloc_2071_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v_a_1994_; lean_object* v_a_1995_; 
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*3, v___x_1986_);
lean_inc_ref(v_a_1958_);
lean_inc(v_a_1957_);
lean_inc(v_a_1956_);
lean_inc(v_a_1955_);
v___x_1992_ = lean_apply_7(v_build_1952_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v___x_1991_, lean_box(0));
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1999_; lean_object* v_a_2000_; lean_object* v_log_2001_; uint8_t v_action_2002_; uint8_t v_wantsRebuild_2003_; lean_object* v_trace_2004_; lean_object* v_buildTime_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_a_1999_ = lean_ctor_get(v___x_1992_, 1);
lean_inc(v_a_1999_);
v_a_2000_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_n(v_a_2000_, 2);
lean_dec_ref_known(v___x_1992_, 2);
v_log_2001_ = lean_ctor_get(v_a_1999_, 0);
v_action_2002_ = lean_ctor_get_uint8(v_a_1999_, sizeof(void*)*3);
v_wantsRebuild_2003_ = lean_ctor_get_uint8(v_a_1999_, sizeof(void*)*3 + 1);
v_trace_2004_ = lean_ctor_get(v_a_1999_, 1);
v_buildTime_2005_ = lean_ctor_get(v_a_1999_, 2);
v___x_2006_ = lean_array_get_size(v_log_1977_);
lean_dec_ref(v_log_1977_);
v___x_2007_ = lean_array_get_size(v_log_2001_);
v___x_2008_ = l_Array_extract___redArg(v_log_2001_, v___x_2006_, v___x_2007_);
v___x_2009_ = lean_apply_1(v_inst_1949_, v_a_2000_);
v___x_2010_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1950_, v___x_2009_, v___x_2008_);
v___x_2011_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1951_, v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2052_; 
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v___x_2011_, 0);
lean_dec(v_unused_2053_);
v___x_2013_ = v___x_2011_;
v_isShared_2014_ = v_isSharedCheck_2052_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v___x_2011_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2052_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lake_removeFileIfExists(v___x_1988_);
lean_dec_ref(v___x_1988_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2035_; 
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2036_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2035_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2035_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
lean_inc(v_a_2000_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_a_2000_);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2000_);
v___x_2020_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 0, v___x_2020_);
v___x_2022_ = v___x_2013_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v___x_2023_ = l_Lake_buildAction___redArg___lam__0(v___x_1989_, v___x_2022_, v_a_1999_);
lean_dec_ref(v___x_2022_);
lean_dec(v___x_1989_);
v_a_2024_ = lean_ctor_get(v___x_2023_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v___x_2023_, 0);
lean_dec(v_unused_2032_);
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_a_2000_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2000_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
else
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2048_; 
lean_inc(v_buildTime_2005_);
lean_inc_ref(v_trace_2004_);
lean_inc_ref(v_log_2001_);
lean_del_object(v___x_2013_);
lean_dec(v_a_2000_);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_1999_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; 
v_unused_2049_ = lean_ctor_get(v_a_1999_, 2);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_a_1999_, 1);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_a_1999_, 0);
lean_dec(v_unused_2051_);
v___x_2038_ = v_a_1999_;
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v_a_1999_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_a_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v_a_2040_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2041_ = lean_io_error_to_string(v_a_2040_);
v___x_2042_ = 3;
v___x_2043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*1, v___x_2042_);
v___x_2044_ = lean_array_push(v_log_2001_, v___x_2043_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2044_);
v___x_2046_ = v___x_2038_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_trace_2004_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_buildTime_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2047_, sizeof(void*)*3, v_action_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2047_, sizeof(void*)*3 + 1, v_wantsRebuild_2003_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v_a_1994_ = v___x_2007_;
v_a_1995_ = v___x_2046_;
goto v___jp_1993_;
}
}
}
}
}
else
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2065_; 
lean_inc(v_buildTime_2005_);
lean_inc_ref(v_trace_2004_);
lean_inc_ref(v_log_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v___x_1988_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_a_1999_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; 
v_unused_2066_ = lean_ctor_get(v_a_1999_, 2);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_a_1999_, 1);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_a_1999_, 0);
lean_dec(v_unused_2068_);
v___x_2055_ = v_a_1999_;
v_isShared_2056_ = v_isSharedCheck_2065_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_a_1999_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2065_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_a_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v_a_2057_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2058_ = lean_io_error_to_string(v_a_2057_);
v___x_2059_ = 3;
v___x_2060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*1, v___x_2059_);
v___x_2061_ = lean_array_push(v_log_2001_, v___x_2060_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2061_);
v___x_2063_ = v___x_2055_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_trace_2004_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_buildTime_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*3, v_action_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*3 + 1, v_wantsRebuild_2003_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
v_a_1994_ = v___x_2007_;
v_a_1995_ = v___x_2063_;
goto v___jp_1993_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v_a_2070_; 
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_log_1977_);
lean_dec_ref(v_traceFile_1951_);
lean_dec_ref(v_inst_1949_);
v_a_2069_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2069_);
v_a_2070_ = lean_ctor_get(v___x_1992_, 1);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_1992_, 2);
v_a_1994_ = v_a_2069_;
v_a_1995_ = v_a_2070_;
goto v___jp_1993_;
}
v___jp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_a_1998_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = l_Lake_buildAction___redArg___lam__0(v___x_1989_, v___x_1996_, v_a_1995_);
lean_dec(v___x_1989_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
v_a_1962_ = v_a_1994_;
v_a_1963_ = v_a_1998_;
goto v___jp_1961_;
}
}
}
else
{
uint8_t v___x_2072_; 
lean_dec_ref(v_a_1954_);
lean_dec_ref(v_build_1952_);
lean_dec_ref(v_inst_1949_);
v___x_2072_ = l_System_FilePath_pathExists(v_traceFile_1951_);
lean_dec_ref(v_traceFile_1951_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v___x_1988_);
lean_del_object(v___x_1983_);
v_log_1966_ = v_log_1977_;
v_action_1967_ = v___x_1986_;
v_wantsRebuild_1968_ = v_noBuild_1985_;
v_trace_1969_ = v_trace_1980_;
v_buildTime_1970_ = v_buildTime_1981_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2075_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1950_, v___x_2073_, v___x_2074_);
v___x_2076_ = l_Lake_BuildMetadata_writeFile(v___x_1988_, v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_dec_ref_known(v___x_2076_, 1);
lean_del_object(v___x_1983_);
v_log_1966_ = v_log_1977_;
v_action_1967_ = v___x_1986_;
v_wantsRebuild_1968_ = v_noBuild_1985_;
v_trace_1969_ = v_trace_1980_;
v_buildTime_1970_ = v_buildTime_1981_;
goto v___jp_1965_;
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = lean_io_error_to_string(v_a_2077_);
v___x_2079_ = 3;
v___x_2080_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*1, v___x_2079_);
v___x_2081_ = lean_array_get_size(v_log_1977_);
v___x_2082_ = lean_array_push(v_log_1977_, v___x_2080_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2082_);
v___x_2084_ = v___x_1983_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_trace_1980_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_buildTime_1981_);
v___x_2084_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; 
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*3, v___x_1986_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*3 + 1, v_noBuild_1985_);
v___x_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2081_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
return v___x_2085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2088_, lean_object* v_depTrace_2089_, lean_object* v_traceFile_2090_, lean_object* v_build_2091_, lean_object* v_action_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
uint8_t v_action_boxed_2100_; lean_object* v_res_2101_; 
v_action_boxed_2100_ = lean_unbox(v_action_2092_);
v_res_2101_ = l_Lake_buildAction___redArg(v_inst_2088_, v_depTrace_2089_, v_traceFile_2090_, v_build_2091_, v_action_boxed_2100_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_depTrace_2089_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2102_, lean_object* v_inst_2103_, lean_object* v_depTrace_2104_, lean_object* v_traceFile_2105_, lean_object* v_build_2106_, uint8_t v_action_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lake_buildAction___redArg(v_inst_2103_, v_depTrace_2104_, v_traceFile_2105_, v_build_2106_, v_action_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_inst_2117_, lean_object* v_depTrace_2118_, lean_object* v_traceFile_2119_, lean_object* v_build_2120_, lean_object* v_action_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
uint8_t v_action_boxed_2129_; lean_object* v_res_2130_; 
v_action_boxed_2129_ = lean_unbox(v_action_2121_);
v_res_2130_ = l_Lake_buildAction(v_00_u03b1_2116_, v_inst_2117_, v_depTrace_2118_, v_traceFile_2119_, v_build_2120_, v_action_boxed_2129_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_depTrace_2118_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_info_2133_, lean_object* v_depTrace_2134_, lean_object* v_traceFile_2135_, lean_object* v_build_2136_, uint8_t v_action_2137_, lean_object* v_oldTrace_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_log_2146_; uint8_t v_action_2147_; uint8_t v_wantsRebuild_2148_; lean_object* v_trace_2149_; lean_object* v_buildTime_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2217_; 
v_log_2146_ = lean_ctor_get(v_a_2144_, 0);
v_action_2147_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3);
v_wantsRebuild_2148_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3 + 1);
v_trace_2149_ = lean_ctor_get(v_a_2144_, 1);
v_buildTime_2150_ = lean_ctor_get(v_a_2144_, 2);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2152_ = v_a_2144_;
v_isShared_2153_ = v_isSharedCheck_2217_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_buildTime_2150_);
lean_inc(v_trace_2149_);
lean_inc(v_log_2146_);
lean_dec(v_a_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2217_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; 
lean_inc_ref(v_traceFile_2135_);
v___x_2154_ = l_Lake_readTraceFile(v_traceFile_2135_, v_log_2146_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_a_2156_; lean_object* v___x_2158_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
v_a_2156_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2154_, 2);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v_a_2156_);
v___x_2158_ = v___x_2152_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2156_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_trace_2149_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_buildTime_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*3, v_action_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*3 + 1, v_wantsRebuild_2148_);
v___x_2158_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2131_, v_inst_2132_, v_info_2133_, v_depTrace_2134_, v_a_2155_, v_oldTrace_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2194_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_a_2161_ = lean_ctor_get(v___x_2159_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2163_ = v___x_2159_;
v_isShared_2164_ = v_isSharedCheck_2194_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2194_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
uint8_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; uint8_t v___x_2168_; 
v___x_2165_ = 0;
v___x_2166_ = lean_unbox(v_a_2160_);
lean_dec(v_a_2160_);
v___x_2167_ = l_Lake_instDecidableEqOutputStatus(v___x_2166_, v___x_2165_);
v___x_2168_ = lean_bool_not(v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___f_2169_; lean_object* v___x_2170_; 
lean_del_object(v___x_2163_);
v___f_2169_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2170_ = l_Lake_buildAction___redArg(v___f_2169_, v_depTrace_2134_, v_traceFile_2135_, v_build_2136_, v_action_2137_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2161_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2179_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v___x_2170_, 0);
lean_dec(v_unused_2180_);
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = lean_box(v___x_2168_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2171_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2181_ = lean_ctor_get(v___x_2170_, 0);
v_a_2182_ = lean_ctor_get(v___x_2170_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2170_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2170_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v_a_2139_);
lean_dec_ref(v_build_2136_);
lean_dec_ref(v_traceFile_2135_);
v___x_2190_ = lean_box(v___x_2168_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2190_);
v___x_2192_ = v___x_2163_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2161_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_a_2139_);
lean_dec_ref(v_build_2136_);
lean_dec_ref(v_traceFile_2135_);
v_a_2195_ = lean_ctor_get(v___x_2159_, 0);
v_a_2196_ = lean_ctor_get(v___x_2159_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2159_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_inc(v_a_2195_);
lean_dec(v___x_2159_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2195_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v_a_2139_);
lean_dec_ref(v_build_2136_);
lean_dec_ref(v_traceFile_2135_);
lean_dec(v_info_2133_);
lean_dec_ref(v_inst_2132_);
lean_dec_ref(v_inst_2131_);
v_a_2205_ = lean_ctor_get(v___x_2154_, 0);
v_a_2206_ = lean_ctor_get(v___x_2154_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2208_ = v___x_2154_;
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_inc(v_a_2205_);
lean_dec(v___x_2154_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v_a_2206_);
v___x_2211_ = v___x_2152_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2206_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_trace_2149_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_buildTime_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3, v_action_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3 + 1, v_wantsRebuild_2148_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2205_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_info_2220_, lean_object* v_depTrace_2221_, lean_object* v_traceFile_2222_, lean_object* v_build_2223_, lean_object* v_action_2224_, lean_object* v_oldTrace_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
uint8_t v_action_boxed_2233_; lean_object* v_res_2234_; 
v_action_boxed_2233_ = lean_unbox(v_action_2224_);
v_res_2234_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2218_, v_inst_2219_, v_info_2220_, v_depTrace_2221_, v_traceFile_2222_, v_build_2223_, v_action_boxed_2233_, v_oldTrace_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_oldTrace_2225_);
lean_dec_ref(v_depTrace_2221_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_info_2238_, lean_object* v_depTrace_2239_, lean_object* v_traceFile_2240_, lean_object* v_build_2241_, uint8_t v_action_2242_, lean_object* v_oldTrace_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_log_2251_; uint8_t v_action_2252_; uint8_t v_wantsRebuild_2253_; lean_object* v_trace_2254_; lean_object* v_buildTime_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2322_; 
v_log_2251_ = lean_ctor_get(v_a_2249_, 0);
v_action_2252_ = lean_ctor_get_uint8(v_a_2249_, sizeof(void*)*3);
v_wantsRebuild_2253_ = lean_ctor_get_uint8(v_a_2249_, sizeof(void*)*3 + 1);
v_trace_2254_ = lean_ctor_get(v_a_2249_, 1);
v_buildTime_2255_ = lean_ctor_get(v_a_2249_, 2);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2249_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2257_ = v_a_2249_;
v_isShared_2258_ = v_isSharedCheck_2322_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_buildTime_2255_);
lean_inc(v_trace_2254_);
lean_inc(v_log_2251_);
lean_dec(v_a_2249_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2322_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; 
lean_inc_ref(v_traceFile_2240_);
v___x_2259_ = l_Lake_readTraceFile(v_traceFile_2240_, v_log_2251_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2263_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
v_a_2261_ = lean_ctor_get(v___x_2259_, 1);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2259_, 2);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v_a_2261_);
v___x_2263_ = v___x_2257_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2261_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_trace_2254_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_buildTime_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*3, v_action_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*3 + 1, v_wantsRebuild_2253_);
v___x_2263_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2236_, v_inst_2237_, v_info_2238_, v_depTrace_2239_, v_a_2260_, v_oldTrace_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2299_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_a_2266_ = lean_ctor_get(v___x_2264_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2268_ = v___x_2264_;
v_isShared_2269_ = v_isSharedCheck_2299_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2299_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; uint8_t v___x_2271_; uint8_t v___x_2272_; uint8_t v___x_2273_; 
v___x_2270_ = 0;
v___x_2271_ = lean_unbox(v_a_2265_);
lean_dec(v_a_2265_);
v___x_2272_ = l_Lake_instDecidableEqOutputStatus(v___x_2271_, v___x_2270_);
v___x_2273_ = lean_bool_not(v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___f_2274_; lean_object* v___x_2275_; 
lean_del_object(v___x_2268_);
v___f_2274_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2275_ = l_Lake_buildAction___redArg(v___f_2274_, v_depTrace_2239_, v_traceFile_2240_, v_build_2241_, v_action_2242_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2266_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2284_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 1);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v___x_2275_, 0);
lean_dec(v_unused_2285_);
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(v___x_2273_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_a_2276_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
v_a_2286_ = lean_ctor_get(v___x_2275_, 0);
v_a_2287_ = lean_ctor_get(v___x_2275_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2275_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_inc(v_a_2286_);
lean_dec(v___x_2275_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_build_2241_);
lean_dec_ref(v_traceFile_2240_);
v___x_2295_ = lean_box(v___x_2273_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2295_);
v___x_2297_ = v___x_2268_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_a_2266_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_build_2241_);
lean_dec_ref(v_traceFile_2240_);
v_a_2300_ = lean_ctor_get(v___x_2264_, 0);
v_a_2301_ = lean_ctor_get(v___x_2264_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2264_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_inc(v_a_2300_);
lean_dec(v___x_2264_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2300_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_a_2244_);
lean_dec_ref(v_build_2241_);
lean_dec_ref(v_traceFile_2240_);
lean_dec(v_info_2238_);
lean_dec_ref(v_inst_2237_);
lean_dec_ref(v_inst_2236_);
v_a_2310_ = lean_ctor_get(v___x_2259_, 0);
v_a_2311_ = lean_ctor_get(v___x_2259_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2313_ = v___x_2259_;
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_inc(v_a_2310_);
lean_dec(v___x_2259_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v_a_2311_);
v___x_2316_ = v___x_2257_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2311_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_trace_2254_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_buildTime_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3, v_action_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3 + 1, v_wantsRebuild_2253_);
v___x_2316_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2318_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2316_);
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2310_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_info_2326_, lean_object* v_depTrace_2327_, lean_object* v_traceFile_2328_, lean_object* v_build_2329_, lean_object* v_action_2330_, lean_object* v_oldTrace_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
uint8_t v_action_boxed_2339_; lean_object* v_res_2340_; 
v_action_boxed_2339_ = lean_unbox(v_action_2330_);
v_res_2340_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2323_, v_inst_2324_, v_inst_2325_, v_info_2326_, v_depTrace_2327_, v_traceFile_2328_, v_build_2329_, v_action_boxed_2339_, v_oldTrace_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_oldTrace_2331_);
lean_dec_ref(v_depTrace_2327_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_info_2343_, lean_object* v_depTrace_2344_, lean_object* v_traceFile_2345_, lean_object* v_build_2346_, uint8_t v_action_2347_, lean_object* v_oldTrace_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v_log_2360_; uint8_t v_action_2361_; uint8_t v_wantsRebuild_2362_; lean_object* v_trace_2363_; lean_object* v_buildTime_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2403_; 
v_log_2360_ = lean_ctor_get(v_a_2354_, 0);
v_action_2361_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*3);
v_wantsRebuild_2362_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*3 + 1);
v_trace_2363_ = lean_ctor_get(v_a_2354_, 1);
v_buildTime_2364_ = lean_ctor_get(v_a_2354_, 2);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_a_2354_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2366_ = v_a_2354_;
v_isShared_2367_ = v_isSharedCheck_2403_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_buildTime_2364_);
lean_inc(v_trace_2363_);
lean_inc(v_log_2360_);
lean_dec(v_a_2354_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2403_;
goto v_resetjp_2365_;
}
v___jp_2356_:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v_a_2357_);
lean_ctor_set(v___x_2359_, 1, v_a_2358_);
return v___x_2359_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; 
lean_inc_ref(v_traceFile_2345_);
v___x_2368_ = l_Lake_readTraceFile(v_traceFile_2345_, v_log_2360_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
v_a_2370_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2368_, 2);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_a_2370_);
v___x_2372_ = v___x_2366_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2370_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_trace_2363_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_buildTime_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*3, v_action_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2397_, sizeof(void*)*3 + 1, v_wantsRebuild_2362_);
v___x_2372_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2341_, v_inst_2342_, v_info_2343_, v_depTrace_2344_, v_a_2369_, v_oldTrace_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2394_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_a_2375_ = lean_ctor_get(v___x_2373_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2377_ = v___x_2373_;
v_isShared_2378_ = v_isSharedCheck_2394_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2394_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v_a_2381_; uint8_t v___x_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; uint8_t v___x_2388_; 
v___x_2379_ = lean_box(0);
v___x_2385_ = 0;
v___x_2386_ = lean_unbox(v_a_2374_);
lean_dec(v_a_2374_);
v___x_2387_ = l_Lake_instDecidableEqOutputStatus(v___x_2386_, v___x_2385_);
v___x_2388_ = lean_bool_not(v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___f_2389_; lean_object* v___x_2390_; 
v___f_2389_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2390_ = l_Lake_buildAction___redArg(v___f_2389_, v_depTrace_2344_, v_traceFile_2345_, v_build_2346_, v_action_2347_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2375_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 2);
v_a_2381_ = v_a_2391_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2392_; lean_object* v_a_2393_; 
lean_del_object(v___x_2377_);
v_a_2392_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2392_);
v_a_2393_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2390_, 2);
v_a_2357_ = v_a_2392_;
v_a_2358_ = v_a_2393_;
goto v___jp_2356_;
}
}
else
{
lean_dec_ref(v_a_2349_);
lean_dec_ref(v_build_2346_);
lean_dec_ref(v_traceFile_2345_);
v_a_2381_ = v_a_2375_;
goto v___jp_2380_;
}
v___jp_2380_:
{
lean_object* v___x_2383_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 1, v_a_2381_);
lean_ctor_set(v___x_2377_, 0, v___x_2379_);
v___x_2383_ = v___x_2377_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v_a_2396_; 
lean_dec_ref(v_a_2349_);
lean_dec_ref(v_build_2346_);
lean_dec_ref(v_traceFile_2345_);
v_a_2395_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2395_);
v_a_2396_ = lean_ctor_get(v___x_2373_, 1);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2373_, 2);
v_a_2357_ = v_a_2395_;
v_a_2358_ = v_a_2396_;
goto v___jp_2356_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v_a_2399_; lean_object* v___x_2401_; 
lean_dec_ref(v_a_2349_);
lean_dec_ref(v_build_2346_);
lean_dec_ref(v_traceFile_2345_);
lean_dec(v_info_2343_);
lean_dec_ref(v_inst_2342_);
lean_dec_ref(v_inst_2341_);
v_a_2398_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2398_);
v_a_2399_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2368_, 2);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_a_2399_);
v___x_2401_ = v___x_2366_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2399_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_trace_2363_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_buildTime_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2402_, sizeof(void*)*3, v_action_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2402_, sizeof(void*)*3 + 1, v_wantsRebuild_2362_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
v_a_2357_ = v_a_2398_;
v_a_2358_ = v___x_2401_;
goto v___jp_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v_info_2406_, lean_object* v_depTrace_2407_, lean_object* v_traceFile_2408_, lean_object* v_build_2409_, lean_object* v_action_2410_, lean_object* v_oldTrace_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
uint8_t v_action_boxed_2419_; lean_object* v_res_2420_; 
v_action_boxed_2419_ = lean_unbox(v_action_2410_);
v_res_2420_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2404_, v_inst_2405_, v_info_2406_, v_depTrace_2407_, v_traceFile_2408_, v_build_2409_, v_action_boxed_2419_, v_oldTrace_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_oldTrace_2411_);
lean_dec_ref(v_depTrace_2407_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_info_2424_, lean_object* v_depTrace_2425_, lean_object* v_traceFile_2426_, lean_object* v_build_2427_, uint8_t v_action_2428_, lean_object* v_oldTrace_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_a_2438_; lean_object* v_a_2439_; lean_object* v_log_2441_; uint8_t v_action_2442_; uint8_t v_wantsRebuild_2443_; lean_object* v_trace_2444_; lean_object* v_buildTime_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2484_; 
v_log_2441_ = lean_ctor_get(v_a_2435_, 0);
v_action_2442_ = lean_ctor_get_uint8(v_a_2435_, sizeof(void*)*3);
v_wantsRebuild_2443_ = lean_ctor_get_uint8(v_a_2435_, sizeof(void*)*3 + 1);
v_trace_2444_ = lean_ctor_get(v_a_2435_, 1);
v_buildTime_2445_ = lean_ctor_get(v_a_2435_, 2);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_a_2435_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2447_ = v_a_2435_;
v_isShared_2448_ = v_isSharedCheck_2484_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_buildTime_2445_);
lean_inc(v_trace_2444_);
lean_inc(v_log_2441_);
lean_dec(v_a_2435_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2484_;
goto v_resetjp_2446_;
}
v___jp_2437_:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_a_2438_);
lean_ctor_set(v___x_2440_, 1, v_a_2439_);
return v___x_2440_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; 
lean_inc_ref(v_traceFile_2426_);
v___x_2449_ = l_Lake_readTraceFile(v_traceFile_2426_, v_log_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_a_2451_; lean_object* v___x_2453_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
v_a_2451_ = lean_ctor_get(v___x_2449_, 1);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2449_, 2);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_a_2451_);
v___x_2453_ = v___x_2447_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2451_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_trace_2444_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_buildTime_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*3, v_action_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*3 + 1, v_wantsRebuild_2443_);
v___x_2453_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2422_, v_inst_2423_, v_info_2424_, v_depTrace_2425_, v_a_2450_, v_oldTrace_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2475_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_a_2456_ = lean_ctor_get(v___x_2454_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2475_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2475_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v_a_2462_; uint8_t v___x_2466_; uint8_t v___x_2467_; uint8_t v___x_2468_; uint8_t v___x_2469_; 
v___x_2460_ = lean_box(0);
v___x_2466_ = 0;
v___x_2467_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
v___x_2468_ = l_Lake_instDecidableEqOutputStatus(v___x_2467_, v___x_2466_);
v___x_2469_ = lean_bool_not(v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___f_2470_; lean_object* v___x_2471_; 
v___f_2470_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2471_ = l_Lake_buildAction___redArg(v___f_2470_, v_depTrace_2425_, v_traceFile_2426_, v_build_2427_, v_action_2428_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2456_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 2);
v_a_2462_ = v_a_2472_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2473_; lean_object* v_a_2474_; 
lean_del_object(v___x_2458_);
v_a_2473_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2473_);
v_a_2474_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2471_, 2);
v_a_2438_ = v_a_2473_;
v_a_2439_ = v_a_2474_;
goto v___jp_2437_;
}
}
else
{
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_build_2427_);
lean_dec_ref(v_traceFile_2426_);
v_a_2462_ = v_a_2456_;
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v_a_2462_);
lean_ctor_set(v___x_2458_, 0, v___x_2460_);
v___x_2464_ = v___x_2458_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_a_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v_a_2477_; 
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_build_2427_);
lean_dec_ref(v_traceFile_2426_);
v_a_2476_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2476_);
v_a_2477_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2454_, 2);
v_a_2438_ = v_a_2476_;
v_a_2439_ = v_a_2477_;
goto v___jp_2437_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v_a_2480_; lean_object* v___x_2482_; 
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_build_2427_);
lean_dec_ref(v_traceFile_2426_);
lean_dec(v_info_2424_);
lean_dec_ref(v_inst_2423_);
lean_dec_ref(v_inst_2422_);
v_a_2479_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2479_);
v_a_2480_ = lean_ctor_get(v___x_2449_, 1);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2449_, 2);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_a_2480_);
v___x_2482_ = v___x_2447_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2480_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_trace_2444_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_buildTime_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*3, v_action_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*3 + 1, v_wantsRebuild_2443_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
v_a_2438_ = v_a_2479_;
v_a_2439_ = v___x_2482_;
goto v___jp_2437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_info_2488_, lean_object* v_depTrace_2489_, lean_object* v_traceFile_2490_, lean_object* v_build_2491_, lean_object* v_action_2492_, lean_object* v_oldTrace_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
uint8_t v_action_boxed_2501_; lean_object* v_res_2502_; 
v_action_boxed_2501_ = lean_unbox(v_action_2492_);
v_res_2502_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2485_, v_inst_2486_, v_inst_2487_, v_info_2488_, v_depTrace_2489_, v_traceFile_2490_, v_build_2491_, v_action_boxed_2501_, v_oldTrace_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_oldTrace_2493_);
lean_dec_ref(v_depTrace_2489_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2504_, uint64_t v_hash_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v_hashFile_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2508_ = lean_string_append(v_file_2504_, v___x_2507_);
lean_inc_ref(v_hashFile_2508_);
v___x_2509_ = l_Lake_createParentDirs(v_hashFile_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref_known(v___x_2509_, 1);
v___x_2510_ = l_Lake_lowerHexUInt64(v_hash_2505_);
v___x_2511_ = l_IO_FS_writeFile(v_hashFile_2508_, v___x_2510_);
lean_dec_ref(v___x_2510_);
lean_dec_ref(v_hashFile_2508_);
return v___x_2511_;
}
else
{
lean_dec_ref(v_hashFile_2508_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2512_, lean_object* v_hash_2513_, lean_object* v_a_2514_){
_start:
{
uint64_t v_hash_boxed_2515_; lean_object* v_res_2516_; 
v_hash_boxed_2515_ = lean_unbox_uint64(v_hash_2513_);
lean_dec_ref(v_hash_2513_);
v_res_2516_ = l_Lake_writeFileHash(v_file_2512_, v_hash_boxed_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2517_, uint8_t v_text_2518_){
_start:
{
lean_object* v___y_2521_; 
if (v_text_2518_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lake_computeBinFileHash(v_file_2517_);
v___y_2521_ = v___x_2533_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lake_computeTextFileHash(v_file_2517_);
v___y_2521_ = v___x_2534_;
goto v___jp_2520_;
}
v___jp_2520_:
{
if (lean_obj_tag(v___y_2521_) == 0)
{
lean_object* v_a_2522_; uint64_t v___x_2523_; lean_object* v___x_2524_; 
v_a_2522_ = lean_ctor_get(v___y_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___y_2521_, 1);
v___x_2523_ = lean_unbox_uint64(v_a_2522_);
lean_dec(v_a_2522_);
v___x_2524_ = l_Lake_writeFileHash(v_file_2517_, v___x_2523_);
return v___x_2524_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v_file_2517_);
v_a_2525_ = lean_ctor_get(v___y_2521_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___y_2521_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___y_2521_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___y_2521_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2535_, lean_object* v_text_2536_, lean_object* v_a_2537_){
_start:
{
uint8_t v_text_boxed_2538_; lean_object* v_res_2539_; 
v_text_boxed_2538_ = lean_unbox(v_text_2536_);
v_res_2539_ = l_Lake_cacheFileHash(v_file_2535_, v_text_boxed_2538_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2543_ = lean_string_append(v_file_2540_, v___x_2542_);
v___x_2544_ = l_Lake_removeFileIfExists(v___x_2543_);
lean_dec_ref(v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lake_clearFileHash(v_file_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2548_, uint8_t v_text_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_toBuildConfig_2553_; uint8_t v_trustHash_2554_; lean_object* v___x_2555_; lean_object* v_hashFile_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2596_; 
v_toBuildConfig_2553_ = lean_ctor_get(v_a_2550_, 0);
v_trustHash_2554_ = lean_ctor_get_uint8(v_toBuildConfig_2553_, sizeof(void*)*3 + 1);
v___x_2555_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2548_);
v_hashFile_2556_ = lean_string_append(v_file_2548_, v___x_2555_);
if (v_trustHash_2554_ == 0)
{
v___y_2596_ = v_a_2551_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lake_Hash_load_x3f(v_hashFile_2556_);
if (lean_obj_tag(v___x_2609_) == 1)
{
lean_object* v_val_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v_hashFile_2556_);
lean_dec_ref(v_file_2548_);
v_val_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_val_2610_);
lean_ctor_set(v___x_2611_, 1, v_a_2551_);
return v___x_2611_;
}
else
{
lean_dec(v___x_2609_);
v___y_2596_ = v_a_2551_;
goto v___jp_2595_;
}
}
v___jp_2557_:
{
if (lean_obj_tag(v___y_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___y_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___y_2563_, 1);
lean_inc_ref(v_hashFile_2556_);
v___x_2565_ = l_Lake_createParentDirs(v_hashFile_2556_);
if (lean_obj_tag(v___x_2565_) == 0)
{
uint64_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2566_ = lean_unbox_uint64(v_a_2564_);
v___x_2567_ = l_Lake_lowerHexUInt64(v___x_2566_);
v___x_2568_ = l_IO_FS_writeFile(v_hashFile_2556_, v___x_2567_);
lean_dec_ref(v___x_2567_);
lean_dec_ref(v_hashFile_2556_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref_known(v___x_2568_, 1);
v___x_2569_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2569_, 0, v___y_2559_);
lean_ctor_set(v___x_2569_, 1, v___y_2558_);
lean_ctor_set(v___x_2569_, 2, v___y_2562_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*3, v___y_2561_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*3 + 1, v___y_2560_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2564_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v_a_2564_);
v_a_2571_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2572_ = lean_io_error_to_string(v_a_2571_);
v___x_2573_ = 3;
v___x_2574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*1, v___x_2573_);
v___x_2575_ = lean_array_get_size(v___y_2559_);
v___x_2576_ = lean_array_push(v___y_2559_, v___x_2574_);
v___x_2577_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___y_2558_);
lean_ctor_set(v___x_2577_, 2, v___y_2562_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*3, v___y_2561_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*3 + 1, v___y_2560_);
v___x_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
return v___x_2578_;
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v_a_2564_);
lean_dec_ref(v_hashFile_2556_);
v_a_2579_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2580_ = lean_io_error_to_string(v_a_2579_);
v___x_2581_ = 3;
v___x_2582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*1, v___x_2581_);
v___x_2583_ = lean_array_get_size(v___y_2559_);
v___x_2584_ = lean_array_push(v___y_2559_, v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___y_2558_);
lean_ctor_set(v___x_2585_, 2, v___y_2562_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3, v___y_2561_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3 + 1, v___y_2560_);
v___x_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec_ref(v_hashFile_2556_);
v_a_2587_ = lean_ctor_get(v___y_2563_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___y_2563_, 1);
v___x_2588_ = lean_io_error_to_string(v_a_2587_);
v___x_2589_ = 3;
v___x_2590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*1, v___x_2589_);
v___x_2591_ = lean_array_get_size(v___y_2559_);
v___x_2592_ = lean_array_push(v___y_2559_, v___x_2590_);
v___x_2593_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___y_2558_);
lean_ctor_set(v___x_2593_, 2, v___y_2562_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3, v___y_2561_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3 + 1, v___y_2560_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
return v___x_2594_;
}
}
v___jp_2595_:
{
if (v_text_2549_ == 0)
{
lean_object* v_log_2597_; uint8_t v_action_2598_; uint8_t v_wantsRebuild_2599_; lean_object* v_trace_2600_; lean_object* v_buildTime_2601_; lean_object* v___x_2602_; 
v_log_2597_ = lean_ctor_get(v___y_2596_, 0);
lean_inc_ref(v_log_2597_);
v_action_2598_ = lean_ctor_get_uint8(v___y_2596_, sizeof(void*)*3);
v_wantsRebuild_2599_ = lean_ctor_get_uint8(v___y_2596_, sizeof(void*)*3 + 1);
v_trace_2600_ = lean_ctor_get(v___y_2596_, 1);
lean_inc_ref(v_trace_2600_);
v_buildTime_2601_ = lean_ctor_get(v___y_2596_, 2);
lean_inc(v_buildTime_2601_);
lean_dec_ref(v___y_2596_);
v___x_2602_ = l_Lake_computeBinFileHash(v_file_2548_);
lean_dec_ref(v_file_2548_);
v___y_2558_ = v_trace_2600_;
v___y_2559_ = v_log_2597_;
v___y_2560_ = v_wantsRebuild_2599_;
v___y_2561_ = v_action_2598_;
v___y_2562_ = v_buildTime_2601_;
v___y_2563_ = v___x_2602_;
goto v___jp_2557_;
}
else
{
lean_object* v_log_2603_; uint8_t v_action_2604_; uint8_t v_wantsRebuild_2605_; lean_object* v_trace_2606_; lean_object* v_buildTime_2607_; lean_object* v___x_2608_; 
v_log_2603_ = lean_ctor_get(v___y_2596_, 0);
lean_inc_ref(v_log_2603_);
v_action_2604_ = lean_ctor_get_uint8(v___y_2596_, sizeof(void*)*3);
v_wantsRebuild_2605_ = lean_ctor_get_uint8(v___y_2596_, sizeof(void*)*3 + 1);
v_trace_2606_ = lean_ctor_get(v___y_2596_, 1);
lean_inc_ref(v_trace_2606_);
v_buildTime_2607_ = lean_ctor_get(v___y_2596_, 2);
lean_inc(v_buildTime_2607_);
lean_dec_ref(v___y_2596_);
v___x_2608_ = l_Lake_computeTextFileHash(v_file_2548_);
lean_dec_ref(v_file_2548_);
v___y_2558_ = v_trace_2606_;
v___y_2559_ = v_log_2603_;
v___y_2560_ = v_wantsRebuild_2605_;
v___y_2561_ = v_action_2604_;
v___y_2562_ = v_buildTime_2607_;
v___y_2563_ = v___x_2608_;
goto v___jp_2557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2612_, lean_object* v_text_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
uint8_t v_text_boxed_2617_; lean_object* v_res_2618_; 
v_text_boxed_2617_ = lean_unbox(v_text_2613_);
v_res_2618_ = l_Lake_fetchFileHash___redArg(v_file_2612_, v_text_boxed_2617_, v_a_2614_, v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2619_, uint8_t v_text_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lake_fetchFileHash___redArg(v_file_2619_, v_text_2620_, v_a_2625_, v_a_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2629_, lean_object* v_text_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_text_boxed_2638_; lean_object* v_res_2639_; 
v_text_boxed_2638_ = lean_unbox(v_text_2630_);
v_res_2639_ = l_Lake_fetchFileHash(v_file_2629_, v_text_boxed_2638_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2640_, uint8_t v_text_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2645_; 
lean_inc_ref(v_file_2640_);
v___x_2645_ = l_Lake_fetchFileHash___redArg(v_file_2640_, v_text_2641_, v_a_2642_, v_a_2643_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2684_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 1);
v_a_2647_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2649_ = v___x_2645_;
v_isShared_2650_ = v_isSharedCheck_2684_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2646_);
lean_inc(v_a_2647_);
lean_dec(v___x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2684_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_log_2651_; uint8_t v_action_2652_; uint8_t v_wantsRebuild_2653_; lean_object* v_trace_2654_; lean_object* v_buildTime_2655_; lean_object* v___x_2656_; 
v_log_2651_ = lean_ctor_get(v_a_2646_, 0);
v_action_2652_ = lean_ctor_get_uint8(v_a_2646_, sizeof(void*)*3);
v_wantsRebuild_2653_ = lean_ctor_get_uint8(v_a_2646_, sizeof(void*)*3 + 1);
v_trace_2654_ = lean_ctor_get(v_a_2646_, 1);
v_buildTime_2655_ = lean_ctor_get(v_a_2646_, 2);
v___x_2656_ = lean_io_metadata(v_file_2640_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_modified_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint64_t v___x_2661_; lean_object* v___x_2663_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v_modified_2658_ = lean_ctor_get(v_a_2657_, 1);
lean_inc_ref(v_modified_2658_);
lean_dec(v_a_2657_);
v___x_2659_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2660_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2660_, 0, v_file_2640_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
lean_ctor_set(v___x_2660_, 2, v_modified_2658_);
v___x_2661_ = lean_unbox_uint64(v_a_2647_);
lean_dec(v_a_2647_);
lean_ctor_set_uint64(v___x_2660_, sizeof(void*)*3, v___x_2661_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2660_);
v___x_2663_ = v___x_2649_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_a_2646_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
else
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2680_; 
lean_inc(v_buildTime_2655_);
lean_inc_ref(v_trace_2654_);
lean_inc_ref(v_log_2651_);
lean_dec(v_a_2647_);
lean_dec_ref(v_file_2640_);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; lean_object* v_unused_2682_; lean_object* v_unused_2683_; 
v_unused_2681_ = lean_ctor_get(v_a_2646_, 2);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_a_2646_, 1);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_a_2646_, 0);
lean_dec(v_unused_2683_);
v___x_2666_ = v_a_2646_;
v_isShared_2667_ = v_isSharedCheck_2680_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v_a_2646_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2680_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_a_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2669_ = lean_io_error_to_string(v_a_2668_);
v___x_2670_ = 3;
v___x_2671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*1, v___x_2670_);
v___x_2672_ = lean_array_get_size(v_log_2651_);
v___x_2673_ = lean_array_push(v_log_2651_, v___x_2671_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2673_);
v___x_2675_ = v___x_2666_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_trace_2654_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_buildTime_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, sizeof(void*)*3, v_action_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, sizeof(void*)*3 + 1, v_wantsRebuild_2653_);
v___x_2675_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set_tag(v___x_2649_, 1);
lean_ctor_set(v___x_2649_, 1, v___x_2675_);
lean_ctor_set(v___x_2649_, 0, v___x_2672_);
v___x_2677_ = v___x_2649_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_file_2640_);
v_a_2685_ = lean_ctor_get(v___x_2645_, 0);
v_a_2686_ = lean_ctor_get(v___x_2645_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2645_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_inc(v_a_2685_);
lean_dec(v___x_2645_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2685_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2694_, lean_object* v_text_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
uint8_t v_text_boxed_2699_; lean_object* v_res_2700_; 
v_text_boxed_2699_ = lean_unbox(v_text_2695_);
v_res_2700_ = l_Lake_fetchFileTrace___redArg(v_file_2694_, v_text_boxed_2699_, v_a_2696_, v_a_2697_);
lean_dec_ref(v_a_2696_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2701_, uint8_t v_text_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lake_fetchFileTrace___redArg(v_file_2701_, v_text_2702_, v_a_2707_, v_a_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2711_, lean_object* v_text_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_text_boxed_2720_; lean_object* v_res_2721_; 
v_text_boxed_2720_ = lean_unbox(v_text_2712_);
v_res_2721_ = l_Lake_fetchFileTrace(v_file_2711_, v_text_boxed_2720_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2722_, lean_object* v_a_x3f_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v_log_2727_; uint8_t v_action_2728_; uint8_t v_wantsRebuild_2729_; lean_object* v_trace_2730_; lean_object* v_buildTime_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2742_; 
v___x_2726_ = lean_io_mono_ms_now();
v_log_2727_ = lean_ctor_get(v___y_2724_, 0);
v_action_2728_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*3);
v_wantsRebuild_2729_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*3 + 1);
v_trace_2730_ = lean_ctor_get(v___y_2724_, 1);
v_buildTime_2731_ = lean_ctor_get(v___y_2724_, 2);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___y_2724_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2733_ = v___y_2724_;
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_buildTime_2731_);
lean_inc(v_trace_2730_);
lean_inc(v_log_2727_);
lean_dec(v___y_2724_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2735_ = lean_nat_sub(v___x_2726_, v_val_2722_);
lean_dec(v___x_2726_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_nat_add(v_buildTime_2731_, v___x_2735_);
lean_dec(v___x_2735_);
lean_dec(v_buildTime_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 2, v___x_2737_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_log_2727_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_trace_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v___x_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2741_, sizeof(void*)*3, v_action_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2741_, sizeof(void*)*3 + 1, v_wantsRebuild_2729_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2743_, lean_object* v_a_x3f_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2743_, v_a_x3f_2744_, v___y_2745_);
lean_dec(v_a_x3f_2744_);
lean_dec(v_val_2743_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2748_, lean_object* v_file_2749_, lean_object* v_a_2750_, lean_object* v_depTrace_2751_, lean_object* v_traceFile_2752_, uint8_t v_action_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_a_2761_; lean_object* v_a_2762_; lean_object* v_log_2765_; uint8_t v_action_2766_; uint8_t v_wantsRebuild_2767_; lean_object* v_trace_2768_; lean_object* v_buildTime_2769_; lean_object* v_toBuildConfig_2775_; lean_object* v_log_2776_; uint8_t v_action_2777_; uint8_t v_wantsRebuild_2778_; lean_object* v_trace_2779_; lean_object* v_buildTime_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2903_; 
v_toBuildConfig_2775_ = lean_ctor_get(v_a_2757_, 0);
v_log_2776_ = lean_ctor_get(v_a_2758_, 0);
v_action_2777_ = lean_ctor_get_uint8(v_a_2758_, sizeof(void*)*3);
v_wantsRebuild_2778_ = lean_ctor_get_uint8(v_a_2758_, sizeof(void*)*3 + 1);
v_trace_2779_ = lean_ctor_get(v_a_2758_, 1);
v_buildTime_2780_ = lean_ctor_get(v_a_2758_, 2);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_a_2758_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2782_ = v_a_2758_;
v_isShared_2783_ = v_isSharedCheck_2903_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_buildTime_2780_);
lean_inc(v_trace_2779_);
lean_inc(v_log_2776_);
lean_dec(v_a_2758_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2903_;
goto v_resetjp_2781_;
}
v___jp_2760_:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2761_);
lean_ctor_set(v___x_2763_, 1, v_a_2762_);
return v___x_2763_;
}
v___jp_2764_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2770_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2771_ = lean_array_get_size(v_log_2765_);
v___x_2772_ = lean_array_push(v_log_2765_, v___x_2770_);
v___x_2773_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v_trace_2768_);
lean_ctor_set(v___x_2773_, 2, v_buildTime_2769_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*3, v_action_2766_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*3 + 1, v_wantsRebuild_2767_);
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
return v___x_2774_;
}
v_resetjp_2781_:
{
uint8_t v_noBuild_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_noBuild_2784_ = lean_ctor_get_uint8(v_toBuildConfig_2775_, sizeof(void*)*3 + 2);
v___x_2785_ = l_Lake_JobAction_merge(v_action_2777_, v_action_2753_);
v___x_2786_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2752_);
v___x_2787_ = l_System_FilePath_addExtension(v_traceFile_2752_, v___x_2786_);
if (v_noBuild_2784_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2776_);
if (v_isShared_2783_ == 0)
{
v___x_2790_ = v___x_2782_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_log_2776_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_trace_2779_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_buildTime_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2887_, sizeof(void*)*3 + 1, v_wantsRebuild_2778_);
v___x_2790_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v_a_2793_; lean_object* v_a_2794_; 
lean_ctor_set_uint8(v___x_2790_, sizeof(void*)*3, v___x_2785_);
lean_inc_ref(v_a_2757_);
lean_inc(v_a_2756_);
lean_inc(v_a_2755_);
lean_inc(v_a_2754_);
v___x_2791_ = lean_apply_7(v_build_2748_, v_a_2750_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v___x_2790_, lean_box(0));
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2798_; lean_object* v_log_2799_; uint8_t v_action_2800_; uint8_t v_wantsRebuild_2801_; lean_object* v_trace_2802_; lean_object* v_buildTime_2803_; lean_object* v___x_2804_; 
v_a_2798_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2791_, 2);
v_log_2799_ = lean_ctor_get(v_a_2798_, 0);
v_action_2800_ = lean_ctor_get_uint8(v_a_2798_, sizeof(void*)*3);
v_wantsRebuild_2801_ = lean_ctor_get_uint8(v_a_2798_, sizeof(void*)*3 + 1);
v_trace_2802_ = lean_ctor_get(v_a_2798_, 1);
v_buildTime_2803_ = lean_ctor_get(v_a_2798_, 2);
v___x_2804_ = l_Lake_clearFileHash(v_file_2749_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = lean_array_get_size(v_log_2776_);
lean_dec_ref(v_log_2776_);
v___x_2807_ = lean_array_get_size(v_log_2799_);
v___x_2808_ = l_Array_extract___redArg(v_log_2799_, v___x_2806_, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2751_, v___x_2809_, v___x_2808_);
v___x_2811_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2752_, v___x_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2852_; 
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2811_, 0);
lean_dec(v_unused_2853_);
v___x_2813_ = v___x_2811_;
v_isShared_2814_ = v_isSharedCheck_2852_;
goto v_resetjp_2812_;
}
else
{
lean_dec(v___x_2811_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2852_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lake_removeFileIfExists(v___x_2787_);
lean_dec_ref(v___x_2787_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2835_; 
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2836_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
lean_inc(v_a_2805_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_a_2805_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2805_);
v___x_2820_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
lean_ctor_set(v___x_2813_, 0, v___x_2820_);
v___x_2822_ = v___x_2813_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v___x_2823_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2788_, v___x_2822_, v_a_2798_);
lean_dec_ref(v___x_2822_);
lean_dec(v___x_2788_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2832_);
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_a_2805_);
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2805_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
else
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2848_; 
lean_inc(v_buildTime_2803_);
lean_inc_ref(v_trace_2802_);
lean_inc_ref(v_log_2799_);
lean_del_object(v___x_2813_);
lean_dec(v_a_2805_);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; lean_object* v_unused_2850_; lean_object* v_unused_2851_; 
v_unused_2849_ = lean_ctor_get(v_a_2798_, 2);
lean_dec(v_unused_2849_);
v_unused_2850_ = lean_ctor_get(v_a_2798_, 1);
lean_dec(v_unused_2850_);
v_unused_2851_ = lean_ctor_get(v_a_2798_, 0);
lean_dec(v_unused_2851_);
v___x_2838_ = v_a_2798_;
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_a_2798_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_a_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v_a_2840_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2841_ = lean_io_error_to_string(v_a_2840_);
v___x_2842_ = 3;
v___x_2843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*1, v___x_2842_);
v___x_2844_ = lean_array_push(v_log_2799_, v___x_2843_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2844_);
v___x_2846_ = v___x_2838_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_trace_2802_);
lean_ctor_set(v_reuseFailAlloc_2847_, 2, v_buildTime_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, sizeof(void*)*3, v_action_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, sizeof(void*)*3 + 1, v_wantsRebuild_2801_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v_a_2793_ = v___x_2807_;
v_a_2794_ = v___x_2846_;
goto v___jp_2792_;
}
}
}
}
}
else
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2865_; 
lean_inc(v_buildTime_2803_);
lean_inc_ref(v_trace_2802_);
lean_inc_ref(v_log_2799_);
lean_dec(v_a_2805_);
lean_dec_ref(v___x_2787_);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; lean_object* v_unused_2867_; lean_object* v_unused_2868_; 
v_unused_2866_ = lean_ctor_get(v_a_2798_, 2);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_a_2798_, 1);
lean_dec(v_unused_2867_);
v_unused_2868_ = lean_ctor_get(v_a_2798_, 0);
lean_dec(v_unused_2868_);
v___x_2855_ = v_a_2798_;
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_a_2798_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_a_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v_a_2857_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2858_ = lean_io_error_to_string(v_a_2857_);
v___x_2859_ = 3;
v___x_2860_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*1, v___x_2859_);
v___x_2861_ = lean_array_push(v_log_2799_, v___x_2860_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2861_);
v___x_2863_ = v___x_2855_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_trace_2802_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_buildTime_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*3, v_action_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*3 + 1, v_wantsRebuild_2801_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v_a_2793_ = v___x_2807_;
v_a_2794_ = v___x_2863_;
goto v___jp_2792_;
}
}
}
}
else
{
lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2881_; 
lean_inc(v_buildTime_2803_);
lean_inc_ref(v_trace_2802_);
lean_inc_ref(v_log_2799_);
lean_dec_ref(v___x_2787_);
lean_dec_ref(v_log_2776_);
lean_dec_ref(v_traceFile_2752_);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; lean_object* v_unused_2883_; lean_object* v_unused_2884_; 
v_unused_2882_ = lean_ctor_get(v_a_2798_, 2);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_a_2798_, 1);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_a_2798_, 0);
lean_dec(v_unused_2884_);
v___x_2870_ = v_a_2798_;
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
else
{
lean_dec(v_a_2798_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_a_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2873_ = lean_io_error_to_string(v_a_2872_);
v___x_2874_ = 3;
v___x_2875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*1, v___x_2874_);
v___x_2876_ = lean_array_get_size(v_log_2799_);
v___x_2877_ = lean_array_push(v_log_2799_, v___x_2875_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2877_);
v___x_2879_ = v___x_2870_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_trace_2802_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_buildTime_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*3, v_action_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*3 + 1, v_wantsRebuild_2801_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v_a_2793_ = v___x_2876_;
v_a_2794_ = v___x_2879_;
goto v___jp_2792_;
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v_a_2886_; 
lean_dec_ref(v___x_2787_);
lean_dec_ref(v_log_2776_);
lean_dec_ref(v_traceFile_2752_);
lean_dec_ref(v_file_2749_);
v_a_2885_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2885_);
v_a_2886_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2791_, 2);
v_a_2793_ = v_a_2885_;
v_a_2794_ = v_a_2886_;
goto v___jp_2792_;
}
v___jp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_a_2797_; 
v___x_2795_ = lean_box(0);
v___x_2796_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2788_, v___x_2795_, v_a_2794_);
lean_dec(v___x_2788_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v_a_2761_ = v_a_2793_;
v_a_2762_ = v_a_2797_;
goto v___jp_2760_;
}
}
}
else
{
uint8_t v___x_2888_; 
lean_dec_ref(v_a_2750_);
lean_dec_ref(v_file_2749_);
lean_dec_ref(v_build_2748_);
v___x_2888_ = l_System_FilePath_pathExists(v_traceFile_2752_);
lean_dec_ref(v_traceFile_2752_);
if (v___x_2888_ == 0)
{
lean_dec_ref(v___x_2787_);
lean_del_object(v___x_2782_);
v_log_2765_ = v_log_2776_;
v_action_2766_ = v___x_2785_;
v_wantsRebuild_2767_ = v_noBuild_2784_;
v_trace_2768_ = v_trace_2779_;
v_buildTime_2769_ = v_buildTime_2780_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2889_ = lean_box(0);
v___x_2890_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2891_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2751_, v___x_2889_, v___x_2890_);
v___x_2892_ = l_Lake_BuildMetadata_writeFile(v___x_2787_, v___x_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref_known(v___x_2892_, 1);
lean_del_object(v___x_2782_);
v_log_2765_ = v_log_2776_;
v_action_2766_ = v___x_2785_;
v_wantsRebuild_2767_ = v_noBuild_2784_;
v_trace_2768_ = v_trace_2779_;
v_buildTime_2769_ = v_buildTime_2780_;
goto v___jp_2764_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = lean_io_error_to_string(v_a_2893_);
v___x_2895_ = 3;
v___x_2896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*1, v___x_2895_);
v___x_2897_ = lean_array_get_size(v_log_2776_);
v___x_2898_ = lean_array_push(v_log_2776_, v___x_2896_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2898_);
v___x_2900_ = v___x_2782_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_trace_2779_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_buildTime_2780_);
v___x_2900_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; 
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3, v___x_2785_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 1, v_noBuild_2784_);
v___x_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2897_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
return v___x_2901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2904_, lean_object* v_file_2905_, lean_object* v_a_2906_, lean_object* v_depTrace_2907_, lean_object* v_traceFile_2908_, lean_object* v_action_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v_action_boxed_2916_; lean_object* v_res_2917_; 
v_action_boxed_2916_ = lean_unbox(v_action_2909_);
v_res_2917_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2904_, v_file_2905_, v_a_2906_, v_depTrace_2907_, v_traceFile_2908_, v_action_boxed_2916_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_depTrace_2907_);
return v_res_2917_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2918_, lean_object* v_self_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_io_metadata(v_info_2918_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v_modified_2923_; uint8_t v___x_2924_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v_modified_2923_ = lean_ctor_get(v_a_2922_, 1);
lean_inc_ref(v_modified_2923_);
lean_dec(v_a_2922_);
v___x_2924_ = l_IO_FS_instOrdSystemTime_ord(v_self_2919_, v_modified_2923_);
lean_dec_ref(v_modified_2923_);
if (v___x_2924_ == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = 1;
return v___x_2925_;
}
else
{
uint8_t v___x_2926_; 
v___x_2926_ = 0;
return v___x_2926_;
}
}
else
{
uint8_t v___x_2927_; 
lean_dec_ref_known(v___x_2921_, 1);
v___x_2927_ = 0;
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2928_, lean_object* v_self_2929_, lean_object* v_a_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2928_, v_self_2929_);
lean_dec_ref(v_self_2929_);
lean_dec_ref(v_info_2928_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2933_) == 0)
{
if (lean_obj_tag(v_x_2934_) == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = 1;
return v___x_2935_;
}
else
{
uint8_t v___x_2936_; 
v___x_2936_ = 0;
return v___x_2936_;
}
}
else
{
if (lean_obj_tag(v_x_2934_) == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = 0;
return v___x_2937_;
}
else
{
lean_object* v_val_2938_; lean_object* v_val_2939_; uint64_t v___x_2940_; uint64_t v___x_2941_; uint8_t v___x_2942_; 
v_val_2938_ = lean_ctor_get(v_x_2933_, 0);
v_val_2939_ = lean_ctor_get(v_x_2934_, 0);
v___x_2940_ = lean_unbox_uint64(v_val_2938_);
v___x_2941_ = lean_unbox_uint64(v_val_2939_);
v___x_2942_ = lean_uint64_dec_eq(v___x_2940_, v___x_2941_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_res_2945_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2943_, v_x_2944_);
lean_dec(v_x_2944_);
lean_dec(v_x_2943_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2947_, lean_object* v_depTrace_2948_, lean_object* v_depHash_2949_, lean_object* v_oldTrace_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
uint64_t v_hash_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_hash_2954_ = lean_ctor_get_uint64(v_depTrace_2948_, sizeof(void*)*3);
v___x_2955_ = lean_box_uint64(v_hash_2954_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
v___x_2957_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2956_, v_depHash_2949_);
lean_dec_ref_known(v___x_2956_, 1);
if (v___x_2957_ == 0)
{
lean_object* v_toBuildConfig_2958_; uint8_t v_oldMode_2959_; 
v_toBuildConfig_2958_ = lean_ctor_get(v_a_2951_, 0);
v_oldMode_2959_ = lean_ctor_get_uint8(v_toBuildConfig_2958_, sizeof(void*)*3);
if (v_oldMode_2959_ == 0)
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = 0;
v___x_2961_ = lean_box(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_a_2952_);
return v___x_2962_;
}
else
{
uint8_t v___x_2963_; 
v___x_2963_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2947_, v_oldTrace_2950_);
if (v___x_2963_ == 0)
{
uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = 0;
v___x_2965_ = lean_box(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_a_2952_);
return v___x_2966_;
}
else
{
uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = 1;
v___x_2968_ = lean_box(v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v_a_2952_);
return v___x_2969_;
}
}
}
else
{
uint8_t v___x_2970_; 
v___x_2970_ = l_System_FilePath_pathExists(v_info_2947_);
if (v___x_2970_ == 0)
{
uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = 0;
v___x_2972_ = lean_box(v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_a_2952_);
return v___x_2973_;
}
else
{
uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = 2;
v___x_2975_ = lean_box(v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_a_2952_);
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2977_, lean_object* v_depTrace_2978_, lean_object* v_depHash_2979_, lean_object* v_oldTrace_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2977_, v_depTrace_2978_, v_depHash_2979_, v_oldTrace_2980_, v_a_2981_, v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_oldTrace_2980_);
lean_dec(v_depHash_2979_);
lean_dec_ref(v_depTrace_2978_);
lean_dec_ref(v_info_2977_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_2985_, lean_object* v_info_2986_, lean_object* v_depTrace_2987_, lean_object* v_savedTrace_2988_, lean_object* v_oldTrace_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
if (lean_obj_tag(v_savedTrace_2988_) == 2)
{
lean_object* v_data_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3047_; 
v_data_2996_ = lean_ctor_get(v_savedTrace_2988_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_savedTrace_2988_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_2998_ = v_savedTrace_2988_;
v_isShared_2999_ = v_isSharedCheck_3047_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_data_2996_);
lean_dec(v_savedTrace_2988_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3047_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
uint64_t v_depHash_3000_; lean_object* v_log_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v_depHash_3000_ = lean_ctor_get_uint64(v_data_2996_, sizeof(void*)*3);
v_log_3001_ = lean_ctor_get(v_data_2996_, 2);
lean_inc_ref(v_log_3001_);
lean_dec_ref(v_data_2996_);
v___x_3002_ = lean_box_uint64(v_depHash_3000_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
lean_ctor_set(v___x_2998_, 0, v___x_3002_);
v___x_3004_ = v___x_2998_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; lean_object* v_a_3006_; lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3045_; 
v___x_3005_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2986_, v_depTrace_2987_, v___x_3004_, v_oldTrace_2989_, v_a_2993_, v_a_2994_);
lean_dec_ref(v___x_3004_);
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_a_3007_ = lean_ctor_get(v___x_3005_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3009_ = v___x_3005_;
v_isShared_3010_ = v_isSharedCheck_3045_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3045_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___y_3012_; uint8_t v___x_3016_; uint8_t v___x_3017_; uint8_t v___x_3018_; uint8_t v___x_3019_; 
v___x_3016_ = 0;
v___x_3017_ = lean_unbox(v_a_3006_);
v___x_3018_ = l_Lake_instDecidableEqOutputStatus(v___x_3017_, v___x_3016_);
v___x_3019_ = lean_bool_not(v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec_ref(v_log_3001_);
v___y_3012_ = v_a_3007_;
goto v___jp_3011_;
}
else
{
lean_object* v_log_3020_; uint8_t v_action_3021_; uint8_t v_wantsRebuild_3022_; lean_object* v_trace_3023_; lean_object* v_buildTime_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3044_; 
v_log_3020_ = lean_ctor_get(v_a_3007_, 0);
v_action_3021_ = lean_ctor_get_uint8(v_a_3007_, sizeof(void*)*3);
v_wantsRebuild_3022_ = lean_ctor_get_uint8(v_a_3007_, sizeof(void*)*3 + 1);
v_trace_3023_ = lean_ctor_get(v_a_3007_, 1);
v_buildTime_3024_ = lean_ctor_get(v_a_3007_, 2);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3026_ = v_a_3007_;
v_isShared_3027_ = v_isSharedCheck_3044_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_buildTime_3024_);
lean_inc(v_trace_3023_);
lean_inc(v_log_3020_);
lean_dec(v_a_3007_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3044_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
uint8_t v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3031_; 
v___x_3028_ = 2;
v___x_3029_ = l_Lake_JobAction_merge(v_action_3021_, v___x_3028_);
if (v_isShared_3027_ == 0)
{
v___x_3031_ = v___x_3026_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_log_3020_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_trace_3023_);
lean_ctor_set(v_reuseFailAlloc_3043_, 2, v_buildTime_3024_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, sizeof(void*)*3 + 1, v_wantsRebuild_3022_);
v___x_3031_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; 
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*3, v___x_3029_);
v___x_3032_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3001_, v_a_2985_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v___x_3031_);
lean_dec_ref(v_log_3001_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 1);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 2);
v___y_3012_ = v_a_3033_;
goto v___jp_3011_;
}
else
{
lean_object* v_a_3034_; lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_del_object(v___x_3009_);
lean_dec(v_a_3006_);
v_a_3034_ = lean_ctor_get(v___x_3032_, 0);
v_a_3035_ = lean_ctor_get(v___x_3032_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3032_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_inc(v_a_3034_);
lean_dec(v___x_3032_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3034_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
}
v___jp_3011_:
{
lean_object* v___x_3014_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___y_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3006_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___y_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3048_; uint8_t v_oldMode_3049_; 
lean_dec(v_savedTrace_2988_);
v_toBuildConfig_3048_ = lean_ctor_get(v_a_2993_, 0);
v_oldMode_3049_ = lean_ctor_get_uint8(v_toBuildConfig_3048_, sizeof(void*)*3);
if (v_oldMode_3049_ == 0)
{
uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = 0;
v___x_3051_ = lean_box(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v_a_2994_);
return v___x_3052_;
}
else
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2986_, v_oldTrace_2989_);
if (v___x_3053_ == 0)
{
uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = 0;
v___x_3055_ = lean_box(v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_a_2994_);
return v___x_3056_;
}
else
{
uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = 1;
v___x_3058_ = lean_box(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v_a_2994_);
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3060_, lean_object* v_info_3061_, lean_object* v_depTrace_3062_, lean_object* v_savedTrace_3063_, lean_object* v_oldTrace_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3060_, v_info_3061_, v_depTrace_3062_, v_savedTrace_3063_, v_oldTrace_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_oldTrace_3064_);
lean_dec_ref(v_depTrace_3062_);
lean_dec_ref(v_info_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3073_, lean_object* v_build_3074_, uint8_t v_text_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v_a_3088_; lean_object* v_log_3121_; uint8_t v_action_3122_; uint8_t v_wantsRebuild_3123_; lean_object* v_trace_3124_; lean_object* v_buildTime_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3157_; 
v_log_3121_ = lean_ctor_get(v_a_3081_, 0);
v_action_3122_ = lean_ctor_get_uint8(v_a_3081_, sizeof(void*)*3);
v_wantsRebuild_3123_ = lean_ctor_get_uint8(v_a_3081_, sizeof(void*)*3 + 1);
v_trace_3124_ = lean_ctor_get(v_a_3081_, 1);
v_buildTime_3125_ = lean_ctor_get(v_a_3081_, 2);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_a_3081_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3127_ = v_a_3081_;
v_isShared_3128_ = v_isSharedCheck_3157_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_buildTime_3125_);
lean_inc(v_trace_3124_);
lean_inc(v_log_3121_);
lean_dec(v_a_3081_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3157_;
goto v_resetjp_3126_;
}
v___jp_3083_:
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_a_3084_);
lean_ctor_set(v___x_3086_, 1, v_a_3085_);
return v___x_3086_;
}
v___jp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lake_fetchFileTrace___redArg(v_file_3073_, v_text_3075_, v_a_3080_, v_a_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3111_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 1);
v_a_3091_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3093_ = v___x_3089_;
v_isShared_3094_ = v_isSharedCheck_3111_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3090_);
lean_inc(v_a_3091_);
lean_dec(v___x_3089_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3111_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_log_3095_; uint8_t v_action_3096_; uint8_t v_wantsRebuild_3097_; lean_object* v_buildTime_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3109_; 
v_log_3095_ = lean_ctor_get(v_a_3090_, 0);
v_action_3096_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*3);
v_wantsRebuild_3097_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*3 + 1);
v_buildTime_3098_ = lean_ctor_get(v_a_3090_, 2);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_a_3090_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_a_3090_, 1);
lean_dec(v_unused_3110_);
v___x_3100_ = v_a_3090_;
v_isShared_3101_ = v_isSharedCheck_3109_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_buildTime_3098_);
lean_inc(v_log_3095_);
lean_dec(v_a_3090_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3109_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_box(0);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v_a_3091_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_log_3095_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_a_3091_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_buildTime_3098_);
lean_ctor_set_uint8(v_reuseFailAlloc_3108_, sizeof(void*)*3, v_action_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3108_, sizeof(void*)*3 + 1, v_wantsRebuild_3097_);
v___x_3104_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3106_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v___x_3104_);
lean_ctor_set(v___x_3093_, 0, v___x_3102_);
v___x_3106_ = v___x_3093_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3089_, 0);
v_a_3113_ = lean_ctor_get(v___x_3089_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3089_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_inc(v_a_3112_);
lean_dec(v___x_3089_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3112_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_traceFile_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3073_);
v_traceFile_3130_ = lean_string_append(v_file_3073_, v___x_3129_);
lean_inc_ref(v_traceFile_3130_);
v___x_3131_ = l_Lake_readTraceFile(v_traceFile_3130_, v_log_3121_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v_a_3133_; lean_object* v_mtime_3134_; lean_object* v___x_3136_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
v_a_3133_ = lean_ctor_get(v___x_3131_, 1);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3131_, 2);
v_mtime_3134_ = lean_ctor_get(v_trace_3124_, 2);
lean_inc_ref(v_trace_3124_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v_a_3133_);
v___x_3136_ = v___x_3127_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3133_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_trace_3124_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_buildTime_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, sizeof(void*)*3, v_action_3122_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, sizeof(void*)*3 + 1, v_wantsRebuild_3123_);
v___x_3136_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3076_, v_file_3073_, v_trace_3124_, v_a_3132_, v_mtime_3134_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v___x_3136_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v_a_3139_; uint8_t v___x_3140_; uint8_t v___x_3141_; uint8_t v___x_3142_; uint8_t v___x_3143_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
v_a_3139_ = lean_ctor_get(v___x_3137_, 1);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3137_, 2);
v___x_3140_ = 0;
v___x_3141_ = lean_unbox(v_a_3138_);
lean_dec(v_a_3138_);
v___x_3142_ = l_Lake_instDecidableEqOutputStatus(v___x_3141_, v___x_3140_);
v___x_3143_ = lean_bool_not(v___x_3142_);
if (v___x_3143_ == 0)
{
uint8_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = 5;
lean_inc_ref(v_file_3073_);
v___x_3145_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3074_, v_file_3073_, v_a_3076_, v_trace_3124_, v_traceFile_3130_, v___x_3144_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3139_);
lean_dec_ref(v_trace_3124_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 2);
v_a_3088_ = v_a_3146_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3147_; lean_object* v_a_3148_; 
lean_dec_ref(v_file_3073_);
v_a_3147_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3147_);
v_a_3148_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3145_, 2);
v_a_3084_ = v_a_3147_;
v_a_3085_ = v_a_3148_;
goto v___jp_3083_;
}
}
else
{
lean_dec_ref(v_traceFile_3130_);
lean_dec_ref(v_trace_3124_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_build_3074_);
v_a_3088_ = v_a_3139_;
goto v___jp_3087_;
}
}
else
{
lean_object* v_a_3149_; lean_object* v_a_3150_; 
lean_dec_ref(v_traceFile_3130_);
lean_dec_ref(v_trace_3124_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_build_3074_);
lean_dec_ref(v_file_3073_);
v_a_3149_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3149_);
v_a_3150_ = lean_ctor_get(v___x_3137_, 1);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3137_, 2);
v_a_3084_ = v_a_3149_;
v_a_3085_ = v_a_3150_;
goto v___jp_3083_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; 
lean_dec_ref(v_traceFile_3130_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_build_3074_);
lean_dec_ref(v_file_3073_);
v_a_3152_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3152_);
v_a_3153_ = lean_ctor_get(v___x_3131_, 1);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3131_, 2);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v_a_3153_);
v___x_3155_ = v___x_3127_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3153_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_trace_3124_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_buildTime_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3156_, sizeof(void*)*3, v_action_3122_);
lean_ctor_set_uint8(v_reuseFailAlloc_3156_, sizeof(void*)*3 + 1, v_wantsRebuild_3123_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
v_a_3084_ = v_a_3152_;
v_a_3085_ = v___x_3155_;
goto v___jp_3083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3158_, lean_object* v_build_3159_, lean_object* v_text_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_){
_start:
{
uint8_t v_text_boxed_3168_; lean_object* v_res_3169_; 
v_text_boxed_3168_ = lean_unbox(v_text_3160_);
v_res_3169_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3158_, v_build_3159_, v_text_boxed_3168_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec(v_a_3162_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3170_, lean_object* v_info_3171_, lean_object* v_depTrace_3172_, lean_object* v_depHash_3173_, lean_object* v_oldTrace_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3171_, v_depTrace_3172_, v_depHash_3173_, v_oldTrace_3174_, v_a_3178_, v_a_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3182_, lean_object* v_info_3183_, lean_object* v_depTrace_3184_, lean_object* v_depHash_3185_, lean_object* v_oldTrace_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3182_, v_info_3183_, v_depTrace_3184_, v_depHash_3185_, v_oldTrace_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_oldTrace_3186_);
lean_dec(v_depHash_3185_);
lean_dec_ref(v_depTrace_3184_);
lean_dec_ref(v_info_3183_);
lean_dec_ref(v_a_3182_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3194_, lean_object* v___x_3195_, lean_object* v_file_3196_, uint64_t v___x_3197_, lean_object* v___x_3198_, uint8_t v_useLocalFile_3199_, lean_object* v_____r_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_IO_setAccessRights(v___x_3194_, v___x_3195_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref_known(v___x_3202_, 1);
lean_inc_ref(v_file_3196_);
v___x_3203_ = l_Lake_writeFileHash(v_file_3196_, v___x_3197_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref_known(v___x_3203_, 1);
v___x_3204_ = lean_io_metadata(v___x_3194_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3217_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3207_ = v___x_3204_;
v_isShared_3208_ = v_isSharedCheck_3217_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3217_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_modified_3209_; lean_object* v___y_3211_; 
v_modified_3209_ = lean_ctor_get(v_a_3205_, 1);
lean_inc_ref(v_modified_3209_);
lean_dec(v_a_3205_);
if (v_useLocalFile_3199_ == 0)
{
v___y_3211_ = v___x_3194_;
goto v___jp_3210_;
}
else
{
lean_dec_ref(v___x_3194_);
lean_inc_ref(v_file_3196_);
v___y_3211_ = v_file_3196_;
goto v___jp_3210_;
}
v___jp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3198_);
lean_ctor_set(v___x_3212_, 1, v___y_3211_);
lean_ctor_set(v___x_3212_, 2, v_file_3196_);
lean_ctor_set(v___x_3212_, 3, v_modified_3209_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3213_);
v___x_3215_ = v___x_3207_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_file_3196_);
lean_dec_ref(v___x_3194_);
v_a_3218_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3204_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3204_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_file_3196_);
lean_dec_ref(v___x_3194_);
v_a_3226_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3203_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3203_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_file_3196_);
lean_dec_ref(v___x_3194_);
v_a_3234_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3202_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3202_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v_file_3244_, lean_object* v___x_3245_, lean_object* v___x_3246_, lean_object* v_useLocalFile_3247_, lean_object* v_____r_3248_, lean_object* v___y_3249_){
_start:
{
uint64_t v___x_2969__boxed_3250_; uint8_t v_useLocalFile_boxed_3251_; lean_object* v_res_3252_; 
v___x_2969__boxed_3250_ = lean_unbox_uint64(v___x_3245_);
lean_dec_ref(v___x_3245_);
v_useLocalFile_boxed_3251_ = lean_unbox(v_useLocalFile_3247_);
v_res_3252_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3242_, v___x_3243_, v_file_3244_, v___x_2969__boxed_3250_, v___x_3246_, v_useLocalFile_boxed_3251_, v_____r_3248_);
lean_dec_ref(v___x_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3260_, lean_object* v_file_3261_, lean_object* v_ext_3262_, uint8_t v_text_3263_, uint8_t v_exe_3264_, uint8_t v_useLocalFile_3265_){
_start:
{
lean_object* v_a_3268_; lean_object* v___y_3275_; uint8_t v___x_3286_; 
v___x_3286_ = 1;
if (v_text_3263_ == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = l_IO_FS_readBinFile(v_file_3261_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; uint64_t v___x_3289_; uint64_t v___x_3290_; uint64_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___y_3296_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = l_Lake_Hash_nil;
v___x_3290_ = lean_byte_array_hash(v_a_3288_);
v___x_3291_ = lean_uint64_mix_hash(v___x_3289_, v___x_3290_);
lean_inc_ref(v_ext_3262_);
v___x_3292_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3292_, 0, v_ext_3262_);
lean_ctor_set_uint64(v___x_3292_, sizeof(void*)*1, v___x_3291_);
v___x_3293_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3294_ = l_System_FilePath_join(v_cache_3260_, v___x_3293_);
v___x_3317_ = lean_string_utf8_byte_size(v_ext_3262_);
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3319_ = lean_nat_dec_eq(v___x_3317_, v___x_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3320_ = l_Lake_lowerHexUInt64(v___x_3291_);
v___x_3321_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3322_ = lean_string_append(v___x_3320_, v___x_3321_);
v___x_3323_ = lean_string_append(v___x_3322_, v_ext_3262_);
lean_dec_ref(v_ext_3262_);
v___y_3296_ = v___x_3323_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3324_; 
lean_dec_ref(v_ext_3262_);
v___x_3324_ = l_Lake_lowerHexUInt64(v___x_3291_);
v___y_3296_ = v___x_3324_;
goto v___jp_3295_;
}
v___jp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3297_, 0, v___x_3286_);
lean_ctor_set_uint8(v___x_3297_, 1, v_text_3263_);
lean_ctor_set_uint8(v___x_3297_, 2, v_exe_3264_);
lean_inc_ref_n(v___x_3297_, 2);
v___x_3298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
lean_ctor_set(v___x_3298_, 2, v___x_3297_);
v___x_3299_ = l_IO_setAccessRights(v_file_3261_, v___x_3298_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
lean_dec_ref_known(v___x_3299_, 1);
v___x_3300_ = l_Lake_joinRelative(v___x_3294_, v___y_3296_);
v___x_3301_ = l_System_FilePath_pathExists(v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
lean_inc_ref(v___x_3300_);
v___x_3302_ = l_Lake_createParentDirs(v___x_3300_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v___x_3303_; 
lean_dec_ref_known(v___x_3302_, 1);
v___x_3303_ = lean_io_hard_link(v_file_3261_, v___x_3300_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref_known(v___x_3303_, 1);
lean_dec(v_a_3288_);
v___x_3304_ = lean_box(0);
v___x_3305_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3300_, v___x_3298_, v_file_3261_, v___x_3291_, v___x_3292_, v_useLocalFile_3265_, v___x_3304_);
lean_dec_ref_known(v___x_3298_, 3);
v___y_3275_ = v___x_3305_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3306_; 
v_a_3306_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3303_, 1);
if (lean_obj_tag(v_a_3306_) == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec_ref_known(v_a_3306_, 2);
lean_dec(v_a_3288_);
v___x_3307_ = lean_box(0);
v___x_3308_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3300_, v___x_3298_, v_file_3261_, v___x_3291_, v___x_3292_, v_useLocalFile_3265_, v___x_3307_);
lean_dec_ref_known(v___x_3298_, 3);
v___y_3275_ = v___x_3308_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3309_; 
lean_dec(v_a_3306_);
v___x_3309_ = l_Lake_writeBinFileIfNew(v___x_3300_, v_a_3288_);
lean_dec(v_a_3288_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3311_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3311_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3300_, v___x_3298_, v_file_3261_, v___x_3291_, v___x_3292_, v_useLocalFile_3265_, v_a_3310_);
lean_dec_ref_known(v___x_3298_, 3);
v___y_3275_ = v___x_3311_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3312_; 
lean_dec_ref(v___x_3300_);
lean_dec_ref_known(v___x_3298_, 3);
lean_dec_ref_known(v___x_3292_, 1);
lean_dec_ref(v_file_3261_);
v_a_3312_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3309_, 1);
v_a_3268_ = v_a_3312_;
goto v___jp_3267_;
}
}
}
}
else
{
lean_object* v_a_3313_; 
lean_dec_ref(v___x_3300_);
lean_dec_ref_known(v___x_3298_, 3);
lean_dec_ref_known(v___x_3292_, 1);
lean_dec(v_a_3288_);
lean_dec_ref(v_file_3261_);
v_a_3313_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3302_, 1);
v_a_3268_ = v_a_3313_;
goto v___jp_3267_;
}
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec(v_a_3288_);
v___x_3314_ = lean_box(0);
v___x_3315_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3300_, v___x_3298_, v_file_3261_, v___x_3291_, v___x_3292_, v_useLocalFile_3265_, v___x_3314_);
lean_dec_ref_known(v___x_3298_, 3);
v___y_3275_ = v___x_3315_;
goto v___jp_3274_;
}
}
else
{
lean_object* v_a_3316_; 
lean_dec_ref_known(v___x_3298_, 3);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_3294_);
lean_dec_ref_known(v___x_3292_, 1);
lean_dec(v_a_3288_);
lean_dec_ref(v_file_3261_);
v_a_3316_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3299_, 1);
v_a_3268_ = v_a_3316_;
goto v___jp_3267_;
}
}
}
else
{
lean_object* v_a_3325_; 
lean_dec_ref(v_ext_3262_);
lean_dec_ref(v_file_3261_);
lean_dec_ref(v_cache_3260_);
v_a_3325_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3287_, 1);
v_a_3268_ = v_a_3325_;
goto v___jp_3267_;
}
}
else
{
lean_object* v___x_3326_; 
v___x_3326_ = l_IO_FS_readFile(v_file_3261_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; uint64_t v___x_3329_; uint64_t v___x_3330_; uint64_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___y_3336_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l_String_crlfToLf(v_a_3327_);
lean_dec(v_a_3327_);
v___x_3329_ = l_Lake_Hash_nil;
v___x_3330_ = lean_string_hash(v___x_3328_);
v___x_3331_ = lean_uint64_mix_hash(v___x_3329_, v___x_3330_);
lean_inc_ref(v_ext_3262_);
v___x_3332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3332_, 0, v_ext_3262_);
lean_ctor_set_uint64(v___x_3332_, sizeof(void*)*1, v___x_3331_);
v___x_3333_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3334_ = l_System_FilePath_join(v_cache_3260_, v___x_3333_);
v___x_3350_ = lean_string_utf8_byte_size(v_ext_3262_);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = lean_nat_dec_eq(v___x_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = l_Lake_lowerHexUInt64(v___x_3331_);
v___x_3354_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3355_ = lean_string_append(v___x_3353_, v___x_3354_);
v___x_3356_ = lean_string_append(v___x_3355_, v_ext_3262_);
lean_dec_ref(v_ext_3262_);
v___y_3336_ = v___x_3356_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3357_; 
lean_dec_ref(v_ext_3262_);
v___x_3357_ = l_Lake_lowerHexUInt64(v___x_3331_);
v___y_3336_ = v___x_3357_;
goto v___jp_3335_;
}
v___jp_3335_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3338_ = l_IO_setAccessRights(v_file_3261_, v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; uint8_t v___x_3340_; 
lean_dec_ref_known(v___x_3338_, 1);
v___x_3339_ = l_Lake_joinRelative(v___x_3334_, v___y_3336_);
v___x_3340_ = l_System_FilePath_pathExists(v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_inc_ref(v___x_3339_);
v___x_3341_ = l_Lake_createParentDirs(v___x_3339_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; 
lean_dec_ref_known(v___x_3341_, 1);
v___x_3342_ = l_Lake_writeFileIfNew(v___x_3339_, v___x_3328_);
lean_dec_ref(v___x_3328_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3339_, v___x_3337_, v_file_3261_, v___x_3331_, v___x_3332_, v_useLocalFile_3265_, v_a_3343_);
v___y_3275_ = v___x_3344_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3345_; 
lean_dec_ref(v___x_3339_);
lean_dec_ref_known(v___x_3332_, 1);
lean_dec_ref(v_file_3261_);
v_a_3345_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3342_, 1);
v_a_3268_ = v_a_3345_;
goto v___jp_3267_;
}
}
else
{
lean_object* v_a_3346_; 
lean_dec_ref(v___x_3339_);
lean_dec_ref_known(v___x_3332_, 1);
lean_dec_ref(v___x_3328_);
lean_dec_ref(v_file_3261_);
v_a_3346_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3341_, 1);
v_a_3268_ = v_a_3346_;
goto v___jp_3267_;
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec_ref(v___x_3328_);
v___x_3347_ = lean_box(0);
v___x_3348_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3339_, v___x_3337_, v_file_3261_, v___x_3331_, v___x_3332_, v_useLocalFile_3265_, v___x_3347_);
v___y_3275_ = v___x_3348_;
goto v___jp_3274_;
}
}
else
{
lean_object* v_a_3349_; 
lean_dec_ref(v___y_3336_);
lean_dec_ref(v___x_3334_);
lean_dec_ref_known(v___x_3332_, 1);
lean_dec_ref(v___x_3328_);
lean_dec_ref(v_file_3261_);
v_a_3349_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3338_, 1);
v_a_3268_ = v_a_3349_;
goto v___jp_3267_;
}
}
}
else
{
lean_object* v_a_3358_; 
lean_dec_ref(v_ext_3262_);
lean_dec_ref(v_file_3261_);
lean_dec_ref(v_cache_3260_);
v_a_3358_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3326_, 1);
v_a_3268_ = v_a_3358_;
goto v___jp_3267_;
}
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3269_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3270_ = lean_io_error_to_string(v_a_3268_);
v___x_3271_ = lean_string_append(v___x_3269_, v___x_3270_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = lean_mk_io_user_error(v___x_3271_);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
v___jp_3274_:
{
if (lean_obj_tag(v___y_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3284_; 
v_a_3276_ = lean_ctor_get(v___y_3275_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3275_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3278_ = v___y_3275_;
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___y_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_a_3280_; lean_object* v___x_3282_; 
v_a_3280_ = lean_ctor_get(v_a_3276_, 0);
lean_inc(v_a_3280_);
lean_dec(v_a_3276_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v_a_3280_);
v___x_3282_ = v___x_3278_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3285_; 
v_a_3285_ = lean_ctor_get(v___y_3275_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___y_3275_, 1);
v_a_3268_ = v_a_3285_;
goto v___jp_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3359_, lean_object* v_file_3360_, lean_object* v_ext_3361_, lean_object* v_text_3362_, lean_object* v_exe_3363_, lean_object* v_useLocalFile_3364_, lean_object* v_a_3365_){
_start:
{
uint8_t v_text_boxed_3366_; uint8_t v_exe_boxed_3367_; uint8_t v_useLocalFile_boxed_3368_; lean_object* v_res_3369_; 
v_text_boxed_3366_ = lean_unbox(v_text_3362_);
v_exe_boxed_3367_ = lean_unbox(v_exe_3363_);
v_useLocalFile_boxed_3368_ = lean_unbox(v_useLocalFile_3364_);
v_res_3369_ = l_Lake_Cache_saveArtifact(v_cache_3359_, v_file_3360_, v_ext_3361_, v_text_boxed_3366_, v_exe_boxed_3367_, v_useLocalFile_boxed_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3370_){
_start:
{
lean_object* v_lakeCache_3371_; 
v_lakeCache_3371_ = lean_ctor_get(v_x_3370_, 2);
lean_inc_ref(v_lakeCache_3371_);
return v_lakeCache_3371_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3372_);
lean_dec_ref(v_x_3372_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3374_, lean_object* v_ext_3375_, uint8_t v_text_3376_, uint8_t v_exe_3377_, uint8_t v_useLocalFile_3378_, lean_object* v_inst_3379_, lean_object* v_____do__lift_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3381_ = lean_box(v_text_3376_);
v___x_3382_ = lean_box(v_exe_3377_);
v___x_3383_ = lean_box(v_useLocalFile_3378_);
v___x_3384_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3384_, 0, v_____do__lift_3380_);
lean_closure_set(v___x_3384_, 1, v_file_3374_);
lean_closure_set(v___x_3384_, 2, v_ext_3375_);
lean_closure_set(v___x_3384_, 3, v___x_3381_);
lean_closure_set(v___x_3384_, 4, v___x_3382_);
lean_closure_set(v___x_3384_, 5, v___x_3383_);
v___x_3385_ = lean_apply_2(v_inst_3379_, lean_box(0), v___x_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3386_, lean_object* v_ext_3387_, lean_object* v_text_3388_, lean_object* v_exe_3389_, lean_object* v_useLocalFile_3390_, lean_object* v_inst_3391_, lean_object* v_____do__lift_3392_){
_start:
{
uint8_t v_text_boxed_3393_; uint8_t v_exe_boxed_3394_; uint8_t v_useLocalFile_boxed_3395_; lean_object* v_res_3396_; 
v_text_boxed_3393_ = lean_unbox(v_text_3388_);
v_exe_boxed_3394_ = lean_unbox(v_exe_3389_);
v_useLocalFile_boxed_3395_ = lean_unbox(v_useLocalFile_3390_);
v_res_3396_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3386_, v_ext_3387_, v_text_boxed_3393_, v_exe_boxed_3394_, v_useLocalFile_boxed_3395_, v_inst_3391_, v_____do__lift_3392_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_file_3401_, lean_object* v_ext_3402_, uint8_t v_text_3403_, uint8_t v_exe_3404_, uint8_t v_useLocalFile_3405_){
_start:
{
lean_object* v_toApplicative_3406_; lean_object* v_toFunctor_3407_; lean_object* v_toBind_3408_; lean_object* v_map_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_toApplicative_3406_ = lean_ctor_get(v_inst_3400_, 0);
v_toFunctor_3407_ = lean_ctor_get(v_toApplicative_3406_, 0);
lean_inc_ref(v_toFunctor_3407_);
v_toBind_3408_ = lean_ctor_get(v_inst_3400_, 1);
lean_inc(v_toBind_3408_);
lean_dec_ref(v_inst_3400_);
v_map_3409_ = lean_ctor_get(v_toFunctor_3407_, 0);
lean_inc(v_map_3409_);
lean_dec_ref(v_toFunctor_3407_);
v___f_3410_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3411_ = lean_box(v_text_3403_);
v___x_3412_ = lean_box(v_exe_3404_);
v___x_3413_ = lean_box(v_useLocalFile_3405_);
v___f_3414_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3414_, 0, v_file_3401_);
lean_closure_set(v___f_3414_, 1, v_ext_3402_);
lean_closure_set(v___f_3414_, 2, v___x_3411_);
lean_closure_set(v___f_3414_, 3, v___x_3412_);
lean_closure_set(v___f_3414_, 4, v___x_3413_);
lean_closure_set(v___f_3414_, 5, v_inst_3399_);
v___x_3415_ = lean_apply_4(v_map_3409_, lean_box(0), lean_box(0), v___f_3410_, v_inst_3398_);
v___x_3416_ = lean_apply_4(v_toBind_3408_, lean_box(0), lean_box(0), v___x_3415_, v___f_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_file_3420_, lean_object* v_ext_3421_, lean_object* v_text_3422_, lean_object* v_exe_3423_, lean_object* v_useLocalFile_3424_){
_start:
{
uint8_t v_text_boxed_3425_; uint8_t v_exe_boxed_3426_; uint8_t v_useLocalFile_boxed_3427_; lean_object* v_res_3428_; 
v_text_boxed_3425_ = lean_unbox(v_text_3422_);
v_exe_boxed_3426_ = lean_unbox(v_exe_3423_);
v_useLocalFile_boxed_3427_ = lean_unbox(v_useLocalFile_3424_);
v_res_3428_ = l_Lake_cacheArtifact___redArg(v_inst_3417_, v_inst_3418_, v_inst_3419_, v_file_3420_, v_ext_3421_, v_text_boxed_3425_, v_exe_boxed_3426_, v_useLocalFile_boxed_3427_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_file_3433_, lean_object* v_ext_3434_, uint8_t v_text_3435_, uint8_t v_exe_3436_, uint8_t v_useLocalFile_3437_){
_start:
{
lean_object* v_toApplicative_3438_; lean_object* v_toFunctor_3439_; lean_object* v_toBind_3440_; lean_object* v_map_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___f_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_toApplicative_3438_ = lean_ctor_get(v_inst_3432_, 0);
v_toFunctor_3439_ = lean_ctor_get(v_toApplicative_3438_, 0);
lean_inc_ref(v_toFunctor_3439_);
v_toBind_3440_ = lean_ctor_get(v_inst_3432_, 1);
lean_inc(v_toBind_3440_);
lean_dec_ref(v_inst_3432_);
v_map_3441_ = lean_ctor_get(v_toFunctor_3439_, 0);
lean_inc(v_map_3441_);
lean_dec_ref(v_toFunctor_3439_);
v___f_3442_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3443_ = lean_box(v_text_3435_);
v___x_3444_ = lean_box(v_exe_3436_);
v___x_3445_ = lean_box(v_useLocalFile_3437_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3446_, 0, v_file_3433_);
lean_closure_set(v___f_3446_, 1, v_ext_3434_);
lean_closure_set(v___f_3446_, 2, v___x_3443_);
lean_closure_set(v___f_3446_, 3, v___x_3444_);
lean_closure_set(v___f_3446_, 4, v___x_3445_);
lean_closure_set(v___f_3446_, 5, v_inst_3431_);
v___x_3447_ = lean_apply_4(v_map_3441_, lean_box(0), lean_box(0), v___f_3442_, v_inst_3430_);
v___x_3448_ = lean_apply_4(v_toBind_3440_, lean_box(0), lean_box(0), v___x_3447_, v___f_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_file_3453_, lean_object* v_ext_3454_, lean_object* v_text_3455_, lean_object* v_exe_3456_, lean_object* v_useLocalFile_3457_){
_start:
{
uint8_t v_text_boxed_3458_; uint8_t v_exe_boxed_3459_; uint8_t v_useLocalFile_boxed_3460_; lean_object* v_res_3461_; 
v_text_boxed_3458_ = lean_unbox(v_text_3455_);
v_exe_boxed_3459_ = lean_unbox(v_exe_3456_);
v_useLocalFile_boxed_3460_ = lean_unbox(v_useLocalFile_3457_);
v_res_3461_ = l_Lake_cacheArtifact(v_m_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_file_3453_, v_ext_3454_, v_text_boxed_3458_, v_exe_boxed_3459_, v_useLocalFile_boxed_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3463_, lean_object* v_x2_3464_){
_start:
{
lean_object* v_message_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_message_3465_ = lean_ctor_get(v_x2_3464_, 0);
v___x_3466_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3467_ = lean_string_append(v_x1_3463_, v___x_3466_);
v___x_3468_ = lean_string_append(v___x_3467_, v_message_3465_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3469_, lean_object* v_x2_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3469_, v_x2_3470_);
lean_dec_ref(v_x2_3470_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3475_, uint64_t v_inputHash_3476_, lean_object* v_pkg_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_toContext_3485_; lean_object* v_log_3486_; uint8_t v_action_3487_; uint8_t v_wantsRebuild_3488_; lean_object* v_trace_3489_; lean_object* v_buildTime_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3585_; 
v_toContext_3485_ = lean_ctor_get(v_a_3482_, 1);
v_log_3486_ = lean_ctor_get(v_a_3483_, 0);
v_action_3487_ = lean_ctor_get_uint8(v_a_3483_, sizeof(void*)*3);
v_wantsRebuild_3488_ = lean_ctor_get_uint8(v_a_3483_, sizeof(void*)*3 + 1);
v_trace_3489_ = lean_ctor_get(v_a_3483_, 1);
v_buildTime_3490_ = lean_ctor_get(v_a_3483_, 2);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3483_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3492_ = v_a_3483_;
v_isShared_3493_ = v_isSharedCheck_3585_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_buildTime_3490_);
lean_inc(v_trace_3489_);
lean_inc(v_log_3486_);
lean_dec(v_a_3483_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3585_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_lakeCache_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_lakeCache_3494_ = lean_ctor_get(v_toContext_3485_, 2);
v___x_3495_ = l_Lake_Package_cacheScope(v_pkg_3477_);
lean_inc_ref(v_lakeCache_3494_);
v___x_3496_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3494_, v___x_3495_, v_inputHash_3476_, v_log_3486_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3572_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_a_3498_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3500_ = v___x_3496_;
v_isShared_3501_ = v_isSharedCheck_3572_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3572_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_a_3498_);
v___x_3503_ = v___x_3492_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3498_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_trace_3489_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_buildTime_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*3, v_action_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*3 + 1, v_wantsRebuild_3488_);
v___x_3503_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3566_; 
v_val_3504_ = lean_ctor_get(v_a_3497_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3506_ = v_a_3497_;
v_isShared_3507_ = v_isSharedCheck_3566_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_val_3504_);
lean_dec(v_a_3497_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3566_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v_r_3510_; lean_object* v___y_3511_; 
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc(v_a_3480_);
lean_inc(v_a_3479_);
v___x_3508_ = lean_apply_8(v_inst_3475_, v_val_3504_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v___x_3503_, lean_box(0));
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3515_; lean_object* v_a_3516_; lean_object* v___x_3518_; 
v_a_3515_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3515_);
v_a_3516_ = lean_ctor_get(v___x_3508_, 1);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3508_, 2);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v_a_3515_);
v___x_3518_ = v___x_3506_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3515_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
v_r_3510_ = v___x_3518_;
v___y_3511_ = v_a_3516_;
goto v___jp_3509_;
}
}
else
{
lean_object* v_a_3520_; lean_object* v_a_3521_; lean_object* v_log_3522_; uint8_t v_action_3523_; uint8_t v_wantsRebuild_3524_; lean_object* v_trace_3525_; lean_object* v_buildTime_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3565_; 
lean_del_object(v___x_3506_);
v_a_3520_ = lean_ctor_get(v___x_3508_, 1);
lean_inc(v_a_3520_);
v_a_3521_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3508_, 2);
v_log_3522_ = lean_ctor_get(v_a_3520_, 0);
v_action_3523_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*3);
v_wantsRebuild_3524_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*3 + 1);
v_trace_3525_ = lean_ctor_get(v_a_3520_, 1);
v_buildTime_3526_ = lean_ctor_get(v_a_3520_, 2);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3528_ = v_a_3520_;
v_isShared_3529_ = v_isSharedCheck_3565_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_buildTime_3526_);
lean_inc(v_trace_3525_);
lean_inc(v_log_3522_);
lean_dec(v_a_3520_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3565_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___y_3534_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3530_ = lean_array_get_size(v_log_3522_);
lean_inc(v_a_3521_);
v___x_3531_ = l_Array_extract___redArg(v_log_3522_, v_a_3521_, v___x_3530_);
v___x_3532_ = l_Array_shrink___redArg(v_log_3522_, v_a_3521_);
lean_dec(v_a_3521_);
v___x_3542_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3543_ = l_Lake_lowerHexUInt64(v_inputHash_3476_);
v___x_3544_ = lean_unsigned_to_nat(7u);
v___x_3545_ = lean_unsigned_to_nat(0u);
v___x_3546_ = lean_string_utf8_byte_size(v___x_3543_);
lean_inc_ref(v___x_3543_);
v___x_3547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3543_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
lean_ctor_set(v___x_3547_, 2, v___x_3546_);
v___x_3548_ = l_String_Slice_Pos_nextn(v___x_3547_, v___x_3545_, v___x_3544_);
lean_dec_ref_known(v___x_3547_, 3);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3543_);
lean_ctor_set(v___x_3549_, 1, v___x_3545_);
lean_ctor_set(v___x_3549_, 2, v___x_3548_);
v___x_3550_ = l_String_Slice_toString(v___x_3549_);
lean_dec_ref_known(v___x_3549_, 3);
v___x_3551_ = lean_string_append(v___x_3542_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3553_ = lean_string_append(v___x_3551_, v___x_3552_);
v___x_3554_ = lean_array_get_size(v___x_3531_);
v___x_3555_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3556_ = lean_nat_dec_lt(v___x_3545_, v___x_3554_);
if (v___x_3556_ == 0)
{
lean_dec_ref(v___x_3531_);
v___y_3534_ = v___x_3553_;
goto v___jp_3533_;
}
else
{
lean_object* v___f_3557_; uint8_t v___x_3558_; 
v___f_3557_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3558_ = lean_nat_dec_le(v___x_3554_, v___x_3554_);
if (v___x_3558_ == 0)
{
if (v___x_3556_ == 0)
{
lean_dec_ref(v___x_3531_);
v___y_3534_ = v___x_3553_;
goto v___jp_3533_;
}
else
{
size_t v___x_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((size_t)0ULL);
v___x_3560_ = lean_usize_of_nat(v___x_3554_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3555_, v___f_3557_, v___x_3531_, v___x_3559_, v___x_3560_, v___x_3553_);
v___y_3534_ = v___x_3561_;
goto v___jp_3533_;
}
}
else
{
size_t v___x_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = ((size_t)0ULL);
v___x_3563_ = lean_usize_of_nat(v___x_3554_);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3555_, v___f_3557_, v___x_3531_, v___x_3562_, v___x_3563_, v___x_3553_);
v___y_3534_ = v___x_3564_;
goto v___jp_3533_;
}
}
v___jp_3533_:
{
uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3535_ = 2;
v___x_3536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3536_, 0, v___y_3534_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*1, v___x_3535_);
v___x_3537_ = lean_array_push(v___x_3532_, v___x_3536_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3537_);
v___x_3539_ = v___x_3528_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_trace_3525_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_buildTime_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*3, v_action_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3541_, sizeof(void*)*3 + 1, v_wantsRebuild_3524_);
v___x_3539_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_box(0);
v_r_3510_ = v___x_3540_;
v___y_3511_ = v___x_3539_;
goto v___jp_3509_;
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___y_3511_);
lean_ctor_set(v___x_3500_, 0, v_r_3510_);
v___x_3513_ = v___x_3500_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_r_3510_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___y_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3569_; 
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3478_);
lean_dec_ref(v_inst_3475_);
v___x_3567_ = lean_box(0);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3503_);
lean_ctor_set(v___x_3500_, 0, v___x_3567_);
v___x_3569_ = v___x_3500_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v___x_3503_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v_a_3478_);
lean_dec_ref(v_inst_3475_);
v_a_3573_ = lean_ctor_get(v___x_3496_, 0);
v_a_3574_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3576_ = v___x_3496_;
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_inc(v_a_3573_);
lean_dec(v___x_3496_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_a_3574_);
v___x_3579_ = v___x_3492_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3574_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_trace_3489_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_buildTime_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*3, v_action_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*3 + 1, v_wantsRebuild_3488_);
v___x_3579_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3579_);
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3573_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3586_, lean_object* v_inputHash_3587_, lean_object* v_pkg_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
uint64_t v_inputHash_boxed_3596_; lean_object* v_res_3597_; 
v_inputHash_boxed_3596_ = lean_unbox_uint64(v_inputHash_3587_);
lean_dec_ref(v_inputHash_3587_);
v_res_3597_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3586_, v_inputHash_boxed_3596_, v_pkg_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec(v_a_3590_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3598_, lean_object* v_inst_3599_, uint64_t v_inputHash_3600_, lean_object* v_pkg_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3599_, v_inputHash_3600_, v_pkg_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3610_, lean_object* v_inst_3611_, lean_object* v_inputHash_3612_, lean_object* v_pkg_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
uint64_t v_inputHash_boxed_3621_; lean_object* v_res_3622_; 
v_inputHash_boxed_3621_ = lean_unbox_uint64(v_inputHash_3612_);
lean_dec_ref(v_inputHash_3612_);
v_res_3622_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3610_, v_inst_3611_, v_inputHash_boxed_3621_, v_pkg_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec(v_a_3615_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3623_, lean_object* v_____r_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_a_3623_);
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v___y_3630_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3635_, lean_object* v_____r_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3635_, v_____r_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3646_, uint64_t v_inputHash_3647_, lean_object* v_savedTrace_3648_, lean_object* v_pkg_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v___y_3658_; lean_object* v_a_3662_; lean_object* v_a_3663_; lean_object* v___y_3678_; 
if (lean_obj_tag(v_savedTrace_3648_) == 2)
{
lean_object* v_data_3693_; uint64_t v_depHash_3694_; lean_object* v_outputs_x3f_3695_; uint8_t v___x_3696_; 
v_data_3693_ = lean_ctor_get(v_savedTrace_3648_, 0);
lean_inc_ref(v_data_3693_);
lean_dec_ref_known(v_savedTrace_3648_, 1);
v_depHash_3694_ = lean_ctor_get_uint64(v_data_3693_, sizeof(void*)*3);
v_outputs_x3f_3695_ = lean_ctor_get(v_data_3693_, 1);
lean_inc(v_outputs_x3f_3695_);
lean_dec_ref(v_data_3693_);
v___x_3696_ = lean_uint64_dec_eq(v_depHash_3694_, v_inputHash_3647_);
if (v___x_3696_ == 0)
{
lean_dec(v_outputs_x3f_3695_);
lean_dec_ref(v_a_3650_);
lean_dec_ref(v_pkg_3649_);
lean_dec_ref(v_inst_3646_);
v___y_3658_ = v_a_3655_;
goto v___jp_3657_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3695_) == 1)
{
lean_object* v_val_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_val_3697_ = lean_ctor_get(v_outputs_x3f_3695_, 0);
lean_inc_n(v_val_3697_, 2);
lean_dec_ref_known(v_outputs_x3f_3695_, 1);
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3699_, 0, v_val_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc(v_a_3652_);
lean_inc(v_a_3651_);
lean_inc_ref(v_a_3650_);
v___x_3700_ = lean_apply_8(v_inst_3646_, v___x_3699_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, lean_box(0));
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_config_3701_; lean_object* v_a_3702_; lean_object* v_a_3703_; lean_object* v_enableArtifactCache_x3f_3704_; lean_object* v_a_3706_; uint8_t v_a_3710_; lean_object* v_a_3711_; 
v_config_3701_ = lean_ctor_get(v_pkg_3649_, 6);
v_a_3702_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3702_);
v_a_3703_ = lean_ctor_get(v___x_3700_, 1);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3700_, 2);
v_enableArtifactCache_x3f_3704_ = lean_ctor_get(v_config_3701_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3704_) == 0)
{
lean_object* v_toContext_3743_; lean_object* v_lakeEnv_3744_; lean_object* v_enableArtifactCache_x3f_3745_; 
v_toContext_3743_ = lean_ctor_get(v_a_3654_, 1);
v_lakeEnv_3744_ = lean_ctor_get(v_toContext_3743_, 0);
v_enableArtifactCache_x3f_3745_ = lean_ctor_get(v_lakeEnv_3744_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3745_) == 0)
{
lean_object* v_packages_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_config_3749_; lean_object* v_enableArtifactCache_x3f_3750_; 
v_packages_3746_ = lean_ctor_get(v_toContext_3743_, 4);
v___x_3747_ = lean_unsigned_to_nat(0u);
v___x_3748_ = lean_array_fget_borrowed(v_packages_3746_, v___x_3747_);
v_config_3749_ = lean_ctor_get(v___x_3748_, 6);
v_enableArtifactCache_x3f_3750_ = lean_ctor_get(v_config_3749_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3750_) == 0)
{
lean_dec(v_val_3697_);
lean_dec_ref(v_pkg_3649_);
v_a_3706_ = v_a_3703_;
goto v___jp_3705_;
}
else
{
lean_object* v_val_3751_; uint8_t v___x_3752_; 
v_val_3751_ = lean_ctor_get(v_enableArtifactCache_x3f_3750_, 0);
v___x_3752_ = lean_unbox(v_val_3751_);
v_a_3710_ = v___x_3752_;
v_a_3711_ = v_a_3703_;
goto v___jp_3709_;
}
}
else
{
lean_object* v_val_3753_; uint8_t v___x_3754_; 
v_val_3753_ = lean_ctor_get(v_enableArtifactCache_x3f_3745_, 0);
v___x_3754_ = lean_unbox(v_val_3753_);
v_a_3710_ = v___x_3754_;
v_a_3711_ = v_a_3703_;
goto v___jp_3709_;
}
}
else
{
lean_object* v_val_3755_; uint8_t v___x_3756_; 
v_val_3755_ = lean_ctor_get(v_enableArtifactCache_x3f_3704_, 0);
v___x_3756_ = lean_unbox(v_val_3755_);
v_a_3710_ = v___x_3756_;
v_a_3711_ = v_a_3703_;
goto v___jp_3709_;
}
v___jp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_box(0);
v___x_3708_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3702_, v___x_3707_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3706_);
lean_dec_ref(v_a_3650_);
v___y_3678_ = v___x_3708_;
goto v___jp_3677_;
}
v___jp_3709_:
{
if (v_a_3710_ == 0)
{
lean_dec(v_val_3697_);
lean_dec_ref(v_pkg_3649_);
v_a_3706_ = v_a_3711_;
goto v___jp_3705_;
}
else
{
lean_object* v_toContext_3712_; lean_object* v_log_3713_; uint8_t v_action_3714_; uint8_t v_wantsRebuild_3715_; lean_object* v_trace_3716_; lean_object* v_buildTime_3717_; lean_object* v_lakeCache_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; 
v_toContext_3712_ = lean_ctor_get(v_a_3654_, 1);
v_log_3713_ = lean_ctor_get(v_a_3711_, 0);
v_action_3714_ = lean_ctor_get_uint8(v_a_3711_, sizeof(void*)*3);
v_wantsRebuild_3715_ = lean_ctor_get_uint8(v_a_3711_, sizeof(void*)*3 + 1);
v_trace_3716_ = lean_ctor_get(v_a_3711_, 1);
v_buildTime_3717_ = lean_ctor_get(v_a_3711_, 2);
v_lakeCache_3718_ = lean_ctor_get(v_toContext_3712_, 2);
v___x_3719_ = l_Lake_Package_cacheScope(v_pkg_3649_);
v___x_3720_ = 0;
lean_inc_ref(v_lakeCache_3718_);
v___x_3721_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3718_, v___x_3719_, v_inputHash_3647_, v_val_3697_, v___x_3698_, v___x_3698_, v___x_3720_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref_known(v___x_3721_, 1);
v___x_3722_ = lean_box(0);
v___x_3723_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3702_, v___x_3722_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3711_);
lean_dec_ref(v_a_3650_);
v___y_3678_ = v___x_3723_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3739_; 
lean_inc(v_buildTime_3717_);
lean_inc_ref(v_trace_3716_);
lean_inc_ref(v_log_3713_);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_a_3711_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3740_ = lean_ctor_get(v_a_3711_, 2);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_a_3711_, 1);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_a_3711_, 0);
lean_dec(v_unused_3742_);
v___x_3725_ = v_a_3711_;
v_isShared_3726_ = v_isSharedCheck_3739_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v_a_3711_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3739_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
v_a_3727_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3728_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3729_ = lean_io_error_to_string(v_a_3727_);
v___x_3730_ = lean_string_append(v___x_3728_, v___x_3729_);
lean_dec_ref(v___x_3729_);
v___x_3731_ = 2;
v___x_3732_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set_uint8(v___x_3732_, sizeof(void*)*1, v___x_3731_);
v___x_3733_ = lean_box(0);
v___x_3734_ = lean_array_push(v_log_3713_, v___x_3732_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3734_);
v___x_3736_ = v___x_3725_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_trace_3716_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_buildTime_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*3, v_action_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*3 + 1, v_wantsRebuild_3715_);
v___x_3736_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3702_, v___x_3733_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v___x_3736_);
lean_dec_ref(v_a_3650_);
v___y_3678_ = v___x_3737_;
goto v___jp_3677_;
}
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v_a_3758_; 
lean_dec(v_val_3697_);
lean_dec_ref(v_a_3650_);
lean_dec_ref(v_pkg_3649_);
v_a_3757_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3757_);
v_a_3758_ = lean_ctor_get(v___x_3700_, 1);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3700_, 2);
v_a_3662_ = v_a_3757_;
v_a_3663_ = v_a_3758_;
goto v___jp_3661_;
}
}
else
{
lean_dec(v_outputs_x3f_3695_);
lean_dec_ref(v_a_3650_);
lean_dec_ref(v_pkg_3649_);
lean_dec_ref(v_inst_3646_);
v___y_3658_ = v_a_3655_;
goto v___jp_3657_;
}
}
}
else
{
lean_dec_ref(v_a_3650_);
lean_dec_ref(v_pkg_3649_);
lean_dec(v_savedTrace_3648_);
lean_dec_ref(v_inst_3646_);
v___y_3658_ = v_a_3655_;
goto v___jp_3657_;
}
v___jp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___y_3658_);
return v___x_3660_;
}
v___jp_3661_:
{
lean_object* v_log_3664_; uint8_t v_action_3665_; uint8_t v_wantsRebuild_3666_; lean_object* v_trace_3667_; lean_object* v_buildTime_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3676_; 
v_log_3664_ = lean_ctor_get(v_a_3663_, 0);
v_action_3665_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*3);
v_wantsRebuild_3666_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*3 + 1);
v_trace_3667_ = lean_ctor_get(v_a_3663_, 1);
v_buildTime_3668_ = lean_ctor_get(v_a_3663_, 2);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_a_3663_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3670_ = v_a_3663_;
v_isShared_3671_ = v_isSharedCheck_3676_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_buildTime_3668_);
lean_inc(v_trace_3667_);
lean_inc(v_log_3664_);
lean_dec(v_a_3663_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3676_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = l_Array_shrink___redArg(v_log_3664_, v_a_3662_);
lean_dec(v_a_3662_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3672_);
v___x_3674_ = v___x_3670_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_trace_3667_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_buildTime_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3, v_action_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 1, v_wantsRebuild_3666_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
v___y_3658_ = v___x_3674_;
goto v___jp_3657_;
}
}
}
v___jp_3677_:
{
if (lean_obj_tag(v___y_3678_) == 0)
{
lean_object* v_a_3679_; 
v_a_3679_ = lean_ctor_get(v___y_3678_, 0);
if (lean_obj_tag(v_a_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3688_; 
lean_inc_ref(v_a_3679_);
v_a_3680_ = lean_ctor_get(v___y_3678_, 1);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___y_3678_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___y_3678_, 0);
lean_dec(v_unused_3689_);
v___x_3682_ = v___y_3678_;
v_isShared_3683_ = v_isSharedCheck_3688_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___y_3678_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3688_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v_a_3684_; lean_object* v___x_3686_; 
v_a_3684_ = lean_ctor_get(v_a_3679_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v_a_3679_, 1);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v_a_3684_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3684_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_a_3680_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
else
{
lean_object* v_a_3690_; 
v_a_3690_ = lean_ctor_get(v___y_3678_, 1);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___y_3678_, 2);
v___y_3658_ = v_a_3690_;
goto v___jp_3657_;
}
}
else
{
lean_object* v_a_3691_; lean_object* v_a_3692_; 
v_a_3691_ = lean_ctor_get(v___y_3678_, 0);
lean_inc(v_a_3691_);
v_a_3692_ = lean_ctor_get(v___y_3678_, 1);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___y_3678_, 2);
v_a_3662_ = v_a_3691_;
v_a_3663_ = v_a_3692_;
goto v___jp_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3759_, lean_object* v_inputHash_3760_, lean_object* v_savedTrace_3761_, lean_object* v_pkg_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
uint64_t v_inputHash_boxed_3770_; lean_object* v_res_3771_; 
v_inputHash_boxed_3770_ = lean_unbox_uint64(v_inputHash_3760_);
lean_dec_ref(v_inputHash_3760_);
v_res_3771_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3759_, v_inputHash_boxed_3770_, v_savedTrace_3761_, v_pkg_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec(v_a_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3772_, lean_object* v_inst_3773_, uint64_t v_inputHash_3774_, lean_object* v_savedTrace_3775_, lean_object* v_pkg_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3773_, v_inputHash_3774_, v_savedTrace_3775_, v_pkg_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3785_, lean_object* v_inst_3786_, lean_object* v_inputHash_3787_, lean_object* v_savedTrace_3788_, lean_object* v_pkg_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
uint64_t v_inputHash_boxed_3797_; lean_object* v_res_3798_; 
v_inputHash_boxed_3797_ = lean_unbox_uint64(v_inputHash_3787_);
lean_dec_ref(v_inputHash_3787_);
v_res_3798_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3785_, v_inst_3786_, v_inputHash_boxed_3797_, v_savedTrace_3788_, v_pkg_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec(v_a_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3799_, uint64_t v_inputHash_3800_, lean_object* v_savedTrace_3801_, lean_object* v_pkg_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_a_3811_; lean_object* v___y_3812_; lean_object* v___x_3815_; lean_object* v_a_3816_; 
lean_inc_ref(v_a_3803_);
lean_inc_ref(v_pkg_3802_);
lean_inc_ref(v_inst_3799_);
v___x_3815_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3799_, v_inputHash_3800_, v_savedTrace_3801_, v_pkg_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
if (lean_obj_tag(v_a_3816_) == 1)
{
lean_object* v_a_3817_; lean_object* v_val_3818_; 
lean_dec_ref(v_a_3803_);
lean_dec_ref(v_pkg_3802_);
lean_dec_ref(v_inst_3799_);
v_a_3817_ = lean_ctor_get(v___x_3815_, 1);
lean_inc(v_a_3817_);
lean_dec_ref(v___x_3815_);
v_val_3818_ = lean_ctor_get(v_a_3816_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_a_3816_, 1);
v_a_3811_ = v_val_3818_;
v___y_3812_ = v_a_3817_;
goto v___jp_3810_;
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
lean_dec(v_a_3816_);
v_a_3819_ = lean_ctor_get(v___x_3815_, 1);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3815_);
v___x_3820_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3799_, v_inputHash_3800_, v_pkg_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
if (lean_obj_tag(v_a_3821_) == 1)
{
lean_object* v_a_3822_; lean_object* v_val_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3820_, 1);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3820_, 2);
v_val_3823_ = lean_ctor_get(v_a_3821_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v_a_3821_, 1);
v_a_3811_ = v_val_3823_;
v___y_3812_ = v_a_3822_;
goto v___jp_3810_;
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v_a_3821_);
v_a_3824_ = lean_ctor_get(v___x_3820_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v___x_3820_, 0);
lean_dec(v_unused_3833_);
v___x_3826_ = v___x_3820_;
v_isShared_3827_ = v_isSharedCheck_3832_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3820_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3832_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3828_ = lean_box(0);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3828_);
v___x_3830_ = v___x_3826_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_a_3824_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
return v___x_3820_;
}
}
v___jp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v_a_3811_);
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___y_3812_);
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3834_, lean_object* v_inputHash_3835_, lean_object* v_savedTrace_3836_, lean_object* v_pkg_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
uint64_t v_inputHash_boxed_3845_; lean_object* v_res_3846_; 
v_inputHash_boxed_3845_ = lean_unbox_uint64(v_inputHash_3835_);
lean_dec_ref(v_inputHash_3835_);
v_res_3846_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3834_, v_inputHash_boxed_3845_, v_savedTrace_3836_, v_pkg_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec(v_a_3839_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3847_, lean_object* v_inst_3848_, uint64_t v_inputHash_3849_, lean_object* v_savedTrace_3850_, lean_object* v_pkg_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_a_3860_; lean_object* v___y_3861_; lean_object* v___x_3864_; lean_object* v_a_3865_; 
lean_inc_ref(v_a_3852_);
lean_inc_ref(v_pkg_3851_);
lean_inc_ref(v_inst_3848_);
v___x_3864_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3848_, v_inputHash_3849_, v_savedTrace_3850_, v_pkg_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
if (lean_obj_tag(v_a_3865_) == 1)
{
lean_object* v_a_3866_; lean_object* v_val_3867_; 
lean_dec_ref(v_a_3852_);
lean_dec_ref(v_pkg_3851_);
lean_dec_ref(v_inst_3848_);
v_a_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3864_);
v_val_3867_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v_a_3865_, 1);
v_a_3860_ = v_val_3867_;
v___y_3861_ = v_a_3866_;
goto v___jp_3859_;
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3869_; 
lean_dec(v_a_3865_);
v_a_3868_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3864_);
v___x_3869_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3848_, v_inputHash_3849_, v_pkg_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3868_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
if (lean_obj_tag(v_a_3870_) == 1)
{
lean_object* v_a_3871_; lean_object* v_val_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3869_, 1);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3869_, 2);
v_val_3872_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v_a_3870_, 1);
v_a_3860_ = v_val_3872_;
v___y_3861_ = v_a_3871_;
goto v___jp_3859_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3870_);
v_a_3873_ = lean_ctor_get(v___x_3869_, 1);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v___x_3869_, 0);
lean_dec(v_unused_3882_);
v___x_3875_ = v___x_3869_;
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3869_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_box(0);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3877_);
v___x_3879_ = v___x_3875_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_a_3873_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
return v___x_3869_;
}
}
v___jp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3860_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v___y_3861_);
return v___x_3863_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3883_, lean_object* v_inst_3884_, lean_object* v_inputHash_3885_, lean_object* v_savedTrace_3886_, lean_object* v_pkg_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
uint64_t v_inputHash_boxed_3895_; lean_object* v_res_3896_; 
v_inputHash_boxed_3895_ = lean_unbox_uint64(v_inputHash_3885_);
lean_dec_ref(v_inputHash_3885_);
v_res_3896_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3883_, v_inst_3884_, v_inputHash_boxed_3895_, v_savedTrace_3886_, v_pkg_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec(v_a_3889_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3897_, lean_object* v___x_3898_, lean_object* v_mtime_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref(v___x_3898_);
v___x_3907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3907_, 0, v_descr_3897_);
lean_ctor_set(v___x_3907_, 1, v___x_3898_);
lean_ctor_set(v___x_3907_, 2, v___x_3898_);
lean_ctor_set(v___x_3907_, 3, v_mtime_3899_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___y_3905_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3909_, lean_object* v___x_3910_, lean_object* v_mtime_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lake_resolveArtifact___lam__0(v_descr_3909_, v___x_3910_, v_mtime_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3921_, lean_object* v___f_3922_, lean_object* v_____r_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_log_3931_; uint8_t v_action_3932_; uint8_t v_wantsRebuild_3933_; lean_object* v_trace_3934_; lean_object* v_buildTime_3935_; lean_object* v___x_3936_; 
v_log_3931_ = lean_ctor_get(v___y_3929_, 0);
v_action_3932_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*3);
v_wantsRebuild_3933_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*3 + 1);
v_trace_3934_ = lean_ctor_get(v___y_3929_, 1);
v_buildTime_3935_ = lean_ctor_get(v___y_3929_, 2);
v___x_3936_ = lean_io_metadata(v___x_3921_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v_modified_3938_; lean_object* v___x_3939_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v_modified_3938_ = lean_ctor_get(v_a_3937_, 1);
lean_inc_ref(v_modified_3938_);
lean_dec(v_a_3937_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc(v___y_3925_);
v___x_3939_ = lean_apply_8(v___f_3922_, v_modified_3938_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, lean_box(0));
return v___x_3939_;
}
else
{
lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3955_; 
lean_inc(v_buildTime_3935_);
lean_inc_ref(v_trace_3934_);
lean_inc_ref(v_log_3931_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___f_3922_);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___y_3929_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; 
v_unused_3956_ = lean_ctor_get(v___y_3929_, 2);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v___y_3929_, 1);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v___y_3929_, 0);
lean_dec(v_unused_3958_);
v___x_3941_ = v___y_3929_;
v_isShared_3942_ = v_isSharedCheck_3955_;
goto v_resetjp_3940_;
}
else
{
lean_dec(v___y_3929_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3955_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_a_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v_a_3943_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3936_, 1);
v___x_3944_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3945_ = lean_io_error_to_string(v_a_3943_);
v___x_3946_ = lean_string_append(v___x_3944_, v___x_3945_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = 3;
v___x_3948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set_uint8(v___x_3948_, sizeof(void*)*1, v___x_3947_);
v___x_3949_ = lean_array_get_size(v_log_3931_);
v___x_3950_ = lean_array_push(v_log_3931_, v___x_3948_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3950_);
v___x_3952_ = v___x_3941_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_trace_3934_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_buildTime_3935_);
lean_ctor_set_uint8(v_reuseFailAlloc_3954_, sizeof(void*)*3, v_action_3932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3954_, sizeof(void*)*3 + 1, v_wantsRebuild_3933_);
v___x_3952_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3949_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3959_, lean_object* v___f_3960_, lean_object* v_____r_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lake_resolveArtifact___lam__1(v___x_3959_, v___f_3960_, v_____r_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___x_3959_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3981_, lean_object* v_service_x3f_3982_, lean_object* v_scope_x3f_3983_, uint8_t v_exe_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v___y_3993_; lean_object* v_a_3994_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v_toContext_4000_; lean_object* v_log_4001_; uint8_t v_action_4002_; uint8_t v_wantsRebuild_4003_; lean_object* v_trace_4004_; lean_object* v_buildTime_4005_; lean_object* v_lakeConfig_4006_; lean_object* v_lakeCache_4007_; uint64_t v_hash_4008_; lean_object* v_ext_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___y_4013_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v_toContext_4000_ = lean_ctor_get(v_a_3989_, 1);
v_log_4001_ = lean_ctor_get(v_a_3990_, 0);
v_action_4002_ = lean_ctor_get_uint8(v_a_3990_, sizeof(void*)*3);
v_wantsRebuild_4003_ = lean_ctor_get_uint8(v_a_3990_, sizeof(void*)*3 + 1);
v_trace_4004_ = lean_ctor_get(v_a_3990_, 1);
v_buildTime_4005_ = lean_ctor_get(v_a_3990_, 2);
v_lakeConfig_4006_ = lean_ctor_get(v_toContext_4000_, 1);
v_lakeCache_4007_ = lean_ctor_get(v_toContext_4000_, 2);
v_hash_4008_ = lean_ctor_get_uint64(v_descr_3981_, sizeof(void*)*1);
v_ext_4009_ = lean_ctor_get(v_descr_3981_, 0);
v___x_4010_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4007_);
v___x_4011_ = l_System_FilePath_join(v_lakeCache_4007_, v___x_4010_);
v___x_4111_ = lean_string_utf8_byte_size(v_ext_4009_);
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = lean_nat_dec_eq(v___x_4111_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4114_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___x_4115_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4116_ = lean_string_append(v___x_4114_, v___x_4115_);
v___x_4117_ = lean_string_append(v___x_4116_, v_ext_4009_);
v___y_4013_ = v___x_4117_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___y_4013_ = v___x_4118_;
goto v___jp_4012_;
}
v___jp_3992_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___y_3993_);
lean_ctor_set(v___x_3995_, 1, v_a_3994_);
return v___x_3995_;
}
v___jp_3996_:
{
if (lean_obj_tag(v___y_3998_) == 0)
{
lean_dec(v___y_3997_);
return v___y_3998_;
}
else
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___y_3998_, 1);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___y_3998_, 2);
v___y_3993_ = v___y_3997_;
v_a_3994_ = v_a_3999_;
goto v___jp_3992_;
}
}
v___jp_4012_:
{
lean_object* v___x_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; 
v___x_4014_ = l_Lake_joinRelative(v___x_4011_, v___y_4013_);
lean_inc_ref(v___x_4014_);
lean_inc_ref(v_descr_3981_);
v___f_4015_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4015_, 0, v_descr_3981_);
lean_closure_set(v___f_4015_, 1, v___x_4014_);
v___x_4016_ = lean_io_metadata(v___x_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v_modified_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v___f_4015_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v_modified_4018_ = lean_ctor_get(v_a_4017_, 1);
lean_inc_ref(v_modified_4018_);
lean_dec(v_a_4017_);
v___x_4019_ = l_Lake_resolveArtifact___lam__0(v_descr_3981_, v___x_4014_, v_modified_4018_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec_ref(v_a_3985_);
return v___x_4019_;
}
else
{
lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4107_; 
lean_inc(v_buildTime_4005_);
lean_inc_ref(v_trace_4004_);
lean_inc_ref(v_log_4001_);
lean_dec_ref(v_descr_3981_);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_a_3990_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; lean_object* v_unused_4109_; lean_object* v_unused_4110_; 
v_unused_4108_ = lean_ctor_get(v_a_3990_, 2);
lean_dec(v_unused_4108_);
v_unused_4109_ = lean_ctor_get(v_a_3990_, 1);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_a_3990_, 0);
lean_dec(v_unused_4110_);
v___x_4021_ = v_a_3990_;
v_isShared_4022_ = v_isSharedCheck_4107_;
goto v_resetjp_4020_;
}
else
{
lean_dec(v_a_3990_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4107_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_a_4023_; 
v_a_4023_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4016_, 1);
if (lean_obj_tag(v_a_4023_) == 11)
{
lean_object* v___x_4024_; 
lean_dec_ref_known(v_a_4023_, 2);
v___x_4024_ = lean_array_get_size(v_log_4001_);
if (lean_obj_tag(v_service_x3f_3982_) == 1)
{
lean_object* v_val_4025_; lean_object* v_cacheServices_4026_; uint8_t v___x_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_val_4025_ = lean_ctor_get(v_service_x3f_3982_, 0);
lean_inc_n(v_val_4025_, 2);
lean_dec_ref_known(v_service_x3f_3982_, 1);
v_cacheServices_4026_ = lean_ctor_get(v_lakeConfig_4006_, 3);
v___x_4027_ = 4;
v___x_4028_ = l_Lake_JobAction_merge(v_action_4002_, v___x_4027_);
v___x_4029_ = lean_box(0);
v___x_4030_ = l_Lean_Name_str___override(v___x_4029_, v_val_4025_);
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4026_, v___x_4030_);
lean_dec(v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 1)
{
lean_dec(v_val_4025_);
if (lean_obj_tag(v_scope_x3f_3983_) == 1)
{
lean_object* v_val_4032_; lean_object* v_val_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v_val_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v_val_4033_ = lean_ctor_get(v_scope_x3f_3983_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v_scope_x3f_3983_, 1);
v___x_4034_ = l_Lake_CacheService_artifactUrl(v_hash_4008_, v_val_4032_, v_val_4033_);
v___x_4035_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4036_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___x_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
lean_dec_ref(v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4039_ = lean_string_append(v___x_4037_, v___x_4038_);
v___x_4040_ = lean_string_append(v___x_4039_, v___x_4014_);
v___x_4041_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
v___x_4043_ = lean_string_append(v___x_4042_, v___x_4034_);
v___x_4044_ = 0;
v___x_4045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set_uint8(v___x_4045_, sizeof(void*)*1, v___x_4044_);
v___x_4046_ = lean_array_push(v_log_4001_, v___x_4045_);
lean_inc_ref(v___x_4014_);
v___x_4047_ = l_Lake_downloadArtifactCore(v_hash_4008_, v___x_4034_, v___x_4014_, v___x_4046_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; uint8_t v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 2);
v___x_4049_ = 1;
v___x_4050_ = 0;
v___x_4051_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4051_, 0, v___x_4049_);
lean_ctor_set_uint8(v___x_4051_, 1, v___x_4050_);
lean_ctor_set_uint8(v___x_4051_, 2, v_exe_3984_);
lean_inc_ref_n(v___x_4051_, 2);
v___x_4052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
lean_ctor_set(v___x_4052_, 2, v___x_4051_);
v___x_4053_ = l_IO_setAccessRights(v___x_4014_, v___x_4052_);
lean_dec_ref_known(v___x_4052_, 3);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4055_; 
lean_dec_ref_known(v___x_4053_, 1);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4048_);
v___x_4055_ = v___x_4021_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4048_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4055_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_ctor_set_uint8(v___x_4055_, sizeof(void*)*3, v___x_4028_);
v___x_4056_ = lean_box(0);
v___x_4057_ = l_Lake_resolveArtifact___lam__1(v___x_4014_, v___f_4015_, v___x_4056_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v___x_4055_);
lean_dec_ref(v___x_4014_);
v___y_3997_ = v___x_4024_;
v___y_3998_ = v___x_4057_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4068_; 
v_a_4059_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4060_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4061_ = lean_io_error_to_string(v_a_4059_);
v___x_4062_ = lean_string_append(v___x_4060_, v___x_4061_);
lean_dec_ref(v___x_4061_);
v___x_4063_ = 2;
v___x_4064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*1, v___x_4063_);
v___x_4065_ = lean_box(0);
v___x_4066_ = lean_array_push(v_a_4048_, v___x_4064_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4066_);
v___x_4068_ = v___x_4021_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4070_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4068_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; 
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3, v___x_4028_);
v___x_4069_ = l_Lake_resolveArtifact___lam__1(v___x_4014_, v___f_4015_, v___x_4065_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v___x_4068_);
lean_dec_ref(v___x_4014_);
v___y_3997_ = v___x_4024_;
v___y_3998_ = v___x_4069_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
v_a_4071_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4047_, 2);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4071_);
v___x_4073_ = v___x_4021_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4071_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_ctor_set_uint8(v___x_4073_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4073_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4078_; 
lean_dec_ref_known(v___x_4031_, 1);
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
v___x_4075_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4076_ = lean_array_push(v_log_4001_, v___x_4075_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4076_);
v___x_4078_ = v___x_4021_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4079_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4078_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; 
lean_dec(v___x_4031_);
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
v___x_4080_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4081_ = lean_string_append(v___x_4080_, v_val_4025_);
lean_dec(v_val_4025_);
v___x_4082_ = 3;
v___x_4083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*1, v___x_4082_);
v___x_4084_ = lean_array_push(v_log_4001_, v___x_4083_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4084_);
v___x_4086_ = v___x_4021_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4087_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4086_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v___x_4088_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4089_ = lean_string_append(v___x_4088_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4090_ = 3;
v___x_4091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*1, v___x_4090_);
v___x_4092_ = lean_array_push(v_log_4001_, v___x_4091_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4092_);
v___x_4094_ = v___x_4021_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3, v_action_4002_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4094_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v___x_4096_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4097_ = lean_io_error_to_string(v_a_4023_);
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
lean_dec_ref(v___x_4097_);
v___x_4099_ = 3;
v___x_4100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*1, v___x_4099_);
v___x_4101_ = lean_array_get_size(v_log_4001_);
v___x_4102_ = lean_array_push(v_log_4001_, v___x_4100_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4102_);
v___x_4104_ = v___x_4021_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4106_, sizeof(void*)*3, v_action_4002_);
lean_ctor_set_uint8(v_reuseFailAlloc_4106_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4104_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; 
v___x_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4101_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
return v___x_4105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4119_, lean_object* v_service_x3f_4120_, lean_object* v_scope_x3f_4121_, lean_object* v_exe_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
uint8_t v_exe_boxed_4130_; lean_object* v_res_4131_; 
v_exe_boxed_4130_ = lean_unbox(v_exe_4122_);
v_res_4131_ = l_Lake_resolveArtifact(v_descr_4119_, v_service_x3f_4120_, v_scope_x3f_4121_, v_exe_boxed_4130_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec(v_a_4125_);
lean_dec(v_a_4124_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4134_, uint8_t v_exe_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_data_4143_; lean_object* v_service_x3f_4144_; lean_object* v_scope_x3f_4145_; lean_object* v___x_4146_; 
v_data_4143_ = lean_ctor_get(v_out_4134_, 0);
lean_inc_n(v_data_4143_, 2);
v_service_x3f_4144_ = lean_ctor_get(v_out_4134_, 1);
lean_inc(v_service_x3f_4144_);
v_scope_x3f_4145_ = lean_ctor_get(v_out_4134_, 2);
lean_inc(v_scope_x3f_4145_);
lean_dec_ref(v_out_4134_);
v___x_4146_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4143_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v_log_4148_; uint8_t v_action_4149_; uint8_t v_wantsRebuild_4150_; lean_object* v_trace_4151_; lean_object* v_buildTime_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4174_; 
lean_dec(v_scope_x3f_4145_);
lean_dec(v_service_x3f_4144_);
lean_dec_ref(v_a_4136_);
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
v_log_4148_ = lean_ctor_get(v_a_4141_, 0);
v_action_4149_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*3);
v_wantsRebuild_4150_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*3 + 1);
v_trace_4151_ = lean_ctor_get(v_a_4141_, 1);
v_buildTime_4152_ = lean_ctor_get(v_a_4141_, 2);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_a_4141_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4154_ = v_a_4141_;
v_isShared_4155_ = v_isSharedCheck_4174_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_buildTime_4152_);
lean_inc(v_trace_4151_);
lean_inc(v_log_4148_);
lean_dec(v_a_4141_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4174_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4156_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4157_ = l_Lean_Json_render(v_data_4143_);
v___x_4158_ = lean_unsigned_to_nat(80u);
v___x_4159_ = lean_unsigned_to_nat(2u);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = l_Std_Format_pretty(v___x_4157_, v___x_4158_, v___x_4159_, v___x_4160_);
v___x_4162_ = lean_string_append(v___x_4156_, v___x_4161_);
lean_dec_ref(v___x_4161_);
v___x_4163_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4164_ = lean_string_append(v___x_4162_, v___x_4163_);
v___x_4165_ = lean_string_append(v___x_4164_, v_a_4147_);
lean_dec(v_a_4147_);
v___x_4166_ = 3;
v___x_4167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set_uint8(v___x_4167_, sizeof(void*)*1, v___x_4166_);
v___x_4168_ = lean_array_get_size(v_log_4148_);
v___x_4169_ = lean_array_push(v_log_4148_, v___x_4167_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4169_);
v___x_4171_ = v___x_4154_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_trace_4151_);
lean_ctor_set(v_reuseFailAlloc_4173_, 2, v_buildTime_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*3, v_action_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*3 + 1, v_wantsRebuild_4150_);
v___x_4171_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4168_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
lean_dec(v_data_4143_);
v_a_4175_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4146_, 1);
v___x_4176_ = l_Lake_resolveArtifact(v_a_4175_, v_service_x3f_4144_, v_scope_x3f_4145_, v_exe_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
return v___x_4176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4177_, lean_object* v_exe_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
uint8_t v_exe_boxed_4186_; lean_object* v_res_4187_; 
v_exe_boxed_4186_ = lean_unbox(v_exe_4178_);
v_res_4187_ = l_Lake_resolveArtifactOutput(v_out_4177_, v_exe_boxed_4186_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec(v_a_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4188_, lean_object* v_out_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lake_resolveArtifactOutput(v_out_4189_, v_exe_4188_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4198_, lean_object* v_out_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
uint8_t v_exe_boxed_4207_; lean_object* v_res_4208_; 
v_exe_boxed_4207_ = lean_unbox(v_exe_4198_);
v_res_4208_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4207_, v_out_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec(v___y_4201_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4209_){
_start:
{
lean_object* v___x_4210_; lean_object* v___f_4211_; 
v___x_4210_ = lean_box(v_exe_4209_);
v___f_4211_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4211_, 0, v___x_4210_);
return v___f_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4212_){
_start:
{
uint8_t v_exe_boxed_4213_; lean_object* v_res_4214_; 
v_exe_boxed_4213_ = lean_unbox(v_exe_4212_);
v_res_4214_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4213_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4215_, lean_object* v_ext_4216_, uint8_t v_text_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v___x_4221_; 
lean_inc_ref(v_path_4215_);
v___x_4221_ = l_Lake_fetchFileHash___redArg(v_path_4215_, v_text_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4240_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_a_4223_ = lean_ctor_get(v___x_4221_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4225_ = v___x_4221_;
v_isShared_4226_ = v_isSharedCheck_4240_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4240_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___x_4236_; 
v___x_4236_ = lean_io_metadata(v_path_4215_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v_modified_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v_modified_4238_ = lean_ctor_get(v_a_4237_, 1);
lean_inc_ref(v_modified_4238_);
lean_dec(v_a_4237_);
v___y_4228_ = v_a_4223_;
v___y_4229_ = v_modified_4238_;
goto v___jp_4227_;
}
else
{
lean_object* v___x_4239_; 
lean_dec_ref_known(v___x_4236_, 1);
v___x_4239_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4228_ = v_a_4223_;
v___y_4229_ = v___x_4239_;
goto v___jp_4227_;
}
v___jp_4227_:
{
lean_object* v___x_4230_; uint64_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4230_, 0, v_ext_4216_);
v___x_4231_ = lean_unbox_uint64(v_a_4222_);
lean_dec(v_a_4222_);
lean_ctor_set_uint64(v___x_4230_, sizeof(void*)*1, v___x_4231_);
lean_inc_ref(v_path_4215_);
v___x_4232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v_path_4215_);
lean_ctor_set(v___x_4232_, 2, v_path_4215_);
lean_ctor_set(v___x_4232_, 3, v___y_4229_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 1, v___y_4228_);
lean_ctor_set(v___x_4225_, 0, v___x_4232_);
v___x_4234_ = v___x_4225_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___y_4228_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v_ext_4216_);
lean_dec_ref(v_path_4215_);
v_a_4241_ = lean_ctor_get(v___x_4221_, 0);
v_a_4242_ = lean_ctor_get(v___x_4221_, 1);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4221_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_inc(v_a_4241_);
lean_dec(v___x_4221_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4241_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4250_, lean_object* v_ext_4251_, lean_object* v_text_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
uint8_t v_text_boxed_4256_; lean_object* v_res_4257_; 
v_text_boxed_4256_ = lean_unbox(v_text_4252_);
v_res_4257_ = l_Lake_computeArtifact___redArg(v_path_4250_, v_ext_4251_, v_text_boxed_4256_, v_a_4253_, v_a_4254_);
lean_dec_ref(v_a_4253_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4258_, lean_object* v_ext_4259_, uint8_t v_text_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lake_computeArtifact___redArg(v_path_4258_, v_ext_4259_, v_text_4260_, v_a_4265_, v_a_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4269_, lean_object* v_ext_4270_, lean_object* v_text_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
uint8_t v_text_boxed_4279_; lean_object* v_res_4280_; 
v_text_boxed_4279_ = lean_unbox(v_text_4271_);
v_res_4280_ = l_Lake_computeArtifact(v_path_4269_, v_ext_4270_, v_text_boxed_4279_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4284_, lean_object* v_art_4285_, uint8_t v_exe_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___y_4290_; uint8_t v___x_4303_; 
v___x_4303_ = l_System_FilePath_pathExists(v_file_4284_);
if (v___x_4303_ == 0)
{
lean_object* v_descr_4304_; lean_object* v_path_4305_; lean_object* v___y_4307_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v_descr_4304_ = lean_ctor_get(v_art_4285_, 0);
v_path_4305_ = lean_ctor_get(v_art_4285_, 1);
v___x_4322_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4323_ = lean_string_append(v___x_4322_, v_path_4305_);
v___x_4324_ = 0;
v___x_4325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4325_, 0, v___x_4323_);
lean_ctor_set_uint8(v___x_4325_, sizeof(void*)*1, v___x_4324_);
v___x_4326_ = lean_array_push(v_a_4287_, v___x_4325_);
lean_inc_ref(v_file_4284_);
v___x_4327_ = l_Lake_createParentDirs(v_file_4284_);
if (lean_obj_tag(v___x_4327_) == 0)
{
uint8_t v___x_4328_; lean_object* v___x_4329_; 
lean_dec_ref_known(v___x_4327_, 1);
v___x_4328_ = 1;
v___x_4329_ = lean_io_hard_link(v_path_4305_, v_file_4284_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_dec_ref_known(v___x_4329_, 1);
if (v_exe_4286_ == 0)
{
v___y_4307_ = v___x_4326_;
goto v___jp_4306_;
}
else
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4330_, 0, v___x_4328_);
lean_ctor_set_uint8(v___x_4330_, 1, v___x_4303_);
lean_ctor_set_uint8(v___x_4330_, 2, v_exe_4286_);
lean_inc_ref_n(v___x_4330_, 2);
v___x_4331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
lean_ctor_set(v___x_4331_, 2, v___x_4330_);
v___x_4332_ = l_IO_setAccessRights(v_file_4284_, v___x_4331_);
lean_dec_ref_known(v___x_4331_, 3);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_dec_ref_known(v___x_4332_, 1);
v___y_4307_ = v___x_4326_;
goto v___jp_4306_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
v___x_4334_ = lean_io_error_to_string(v_a_4333_);
v___x_4335_ = 3;
v___x_4336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*1, v___x_4335_);
v___x_4337_ = lean_array_get_size(v___x_4326_);
v___x_4338_ = lean_array_push(v___x_4326_, v___x_4336_);
v___x_4339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4337_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
return v___x_4339_;
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4340_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4329_, 1);
v___x_4341_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4342_ = lean_io_error_to_string(v_a_4340_);
v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
lean_ctor_set_uint8(v___x_4344_, sizeof(void*)*1, v___x_4324_);
v___x_4345_ = lean_array_push(v___x_4326_, v___x_4344_);
v___x_4346_ = l_Lake_copyFile(v_path_4305_, v_file_4284_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
lean_dec_ref_known(v___x_4346_, 1);
v___x_4347_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4347_, 0, v___x_4328_);
lean_ctor_set_uint8(v___x_4347_, 1, v___x_4303_);
lean_ctor_set_uint8(v___x_4347_, 2, v_exe_4286_);
lean_inc_ref_n(v___x_4347_, 2);
v___x_4348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4347_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
lean_ctor_set(v___x_4348_, 2, v___x_4347_);
v___x_4349_ = l_IO_setAccessRights(v_file_4284_, v___x_4348_);
lean_dec_ref_known(v___x_4348_, 3);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_dec_ref_known(v___x_4349_, 1);
v___y_4307_ = v___x_4345_;
goto v___jp_4306_;
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = lean_io_error_to_string(v_a_4350_);
v___x_4352_ = 3;
v___x_4353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set_uint8(v___x_4353_, sizeof(void*)*1, v___x_4352_);
v___x_4354_ = lean_array_get_size(v___x_4345_);
v___x_4355_ = lean_array_push(v___x_4345_, v___x_4353_);
v___x_4356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
return v___x_4356_;
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4357_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4346_, 1);
v___x_4358_ = lean_io_error_to_string(v_a_4357_);
v___x_4359_ = 3;
v___x_4360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*1, v___x_4359_);
v___x_4361_ = lean_array_get_size(v___x_4345_);
v___x_4362_ = lean_array_push(v___x_4345_, v___x_4360_);
v___x_4363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
return v___x_4363_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4364_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4365_ = lean_io_error_to_string(v_a_4364_);
v___x_4366_ = 3;
v___x_4367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4367_, 0, v___x_4365_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*1, v___x_4366_);
v___x_4368_ = lean_array_get_size(v___x_4326_);
v___x_4369_ = lean_array_push(v___x_4326_, v___x_4367_);
v___x_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
return v___x_4370_;
}
v___jp_4306_:
{
uint64_t v_hash_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_hash_4308_ = lean_ctor_get_uint64(v_descr_4304_, sizeof(void*)*1);
v___x_4309_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4310_ = lean_string_append(v___x_4309_, v_file_4284_);
v___x_4311_ = 0;
v___x_4312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4312_, 0, v___x_4310_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*1, v___x_4311_);
v___x_4313_ = lean_array_push(v___y_4307_, v___x_4312_);
lean_inc_ref(v_file_4284_);
v___x_4314_ = l_Lake_writeFileHash(v_file_4284_, v_hash_4308_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_dec_ref_known(v___x_4314_, 1);
v___y_4290_ = v___x_4313_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = lean_io_error_to_string(v_a_4315_);
v___x_4317_ = 3;
v___x_4318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set_uint8(v___x_4318_, sizeof(void*)*1, v___x_4317_);
v___x_4319_ = lean_array_get_size(v___x_4313_);
v___x_4320_ = lean_array_push(v___x_4313_, v___x_4318_);
v___x_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
return v___x_4321_;
}
}
}
else
{
v___y_4290_ = v_a_4287_;
goto v___jp_4289_;
}
v___jp_4289_:
{
lean_object* v_descr_4291_; lean_object* v_mtime_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4300_; 
v_descr_4291_ = lean_ctor_get(v_art_4285_, 0);
v_mtime_4292_ = lean_ctor_get(v_art_4285_, 3);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_art_4285_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; lean_object* v_unused_4302_; 
v_unused_4301_ = lean_ctor_get(v_art_4285_, 2);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_art_4285_, 1);
lean_dec(v_unused_4302_);
v___x_4294_ = v_art_4285_;
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_mtime_4292_);
lean_inc(v_descr_4291_);
lean_dec(v_art_4285_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
lean_inc_ref(v_file_4284_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 2, v_file_4284_);
lean_ctor_set(v___x_4294_, 1, v_file_4284_);
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_descr_4291_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_file_4284_);
lean_ctor_set(v_reuseFailAlloc_4299_, 2, v_file_4284_);
lean_ctor_set(v_reuseFailAlloc_4299_, 3, v_mtime_4292_);
v___x_4297_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; 
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___y_4290_);
return v___x_4298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4371_, lean_object* v_art_4372_, lean_object* v_exe_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
uint8_t v_exe_boxed_4376_; lean_object* v_res_4377_; 
v_exe_boxed_4376_ = lean_unbox(v_exe_4373_);
v_res_4377_ = l_Lake_restoreArtifact(v_file_4371_, v_art_4372_, v_exe_boxed_4376_, v_a_4374_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4378_, lean_object* v_a_x3f_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v_log_4383_; uint8_t v_action_4384_; uint8_t v_wantsRebuild_4385_; lean_object* v_trace_4386_; lean_object* v_buildTime_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4398_; 
v___x_4382_ = lean_io_mono_ms_now();
v_log_4383_ = lean_ctor_get(v___y_4380_, 0);
v_action_4384_ = lean_ctor_get_uint8(v___y_4380_, sizeof(void*)*3);
v_wantsRebuild_4385_ = lean_ctor_get_uint8(v___y_4380_, sizeof(void*)*3 + 1);
v_trace_4386_ = lean_ctor_get(v___y_4380_, 1);
v_buildTime_4387_ = lean_ctor_get(v___y_4380_, 2);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___y_4380_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4389_ = v___y_4380_;
v_isShared_4390_ = v_isSharedCheck_4398_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_buildTime_4387_);
lean_inc(v_trace_4386_);
lean_inc(v_log_4383_);
lean_dec(v___y_4380_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4398_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4391_ = lean_nat_sub(v___x_4382_, v_val_4378_);
lean_dec(v___x_4382_);
v___x_4392_ = lean_box(0);
v___x_4393_ = lean_nat_add(v_buildTime_4387_, v___x_4391_);
lean_dec(v___x_4391_);
lean_dec(v_buildTime_4387_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 2, v___x_4393_);
v___x_4395_ = v___x_4389_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_log_4383_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_trace_4386_);
lean_ctor_set(v_reuseFailAlloc_4397_, 2, v___x_4393_);
lean_ctor_set_uint8(v_reuseFailAlloc_4397_, sizeof(void*)*3, v_action_4384_);
lean_ctor_set_uint8(v_reuseFailAlloc_4397_, sizeof(void*)*3 + 1, v_wantsRebuild_4385_);
v___x_4395_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4396_; 
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4392_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
return v___x_4396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4399_, lean_object* v_a_x3f_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4399_, v_a_x3f_4400_, v___y_4401_);
lean_dec(v_a_x3f_4400_);
lean_dec(v_val_4399_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4404_, lean_object* v_build_4405_, lean_object* v_traceFile_4406_, lean_object* v_ext_4407_, uint8_t v_text_4408_, lean_object* v_a_4409_, lean_object* v_depTrace_4410_, lean_object* v_traceFile_4411_, uint8_t v_action_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v_a_4420_; lean_object* v_a_4421_; lean_object* v_log_4424_; uint8_t v_action_4425_; uint8_t v_wantsRebuild_4426_; lean_object* v_trace_4427_; lean_object* v_buildTime_4428_; lean_object* v_toBuildConfig_4434_; lean_object* v_log_4435_; uint8_t v_action_4436_; uint8_t v_wantsRebuild_4437_; lean_object* v_trace_4438_; lean_object* v_buildTime_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4618_; 
v_toBuildConfig_4434_ = lean_ctor_get(v_a_4416_, 0);
v_log_4435_ = lean_ctor_get(v_a_4417_, 0);
v_action_4436_ = lean_ctor_get_uint8(v_a_4417_, sizeof(void*)*3);
v_wantsRebuild_4437_ = lean_ctor_get_uint8(v_a_4417_, sizeof(void*)*3 + 1);
v_trace_4438_ = lean_ctor_get(v_a_4417_, 1);
v_buildTime_4439_ = lean_ctor_get(v_a_4417_, 2);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_a_4417_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4441_ = v_a_4417_;
v_isShared_4442_ = v_isSharedCheck_4618_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_buildTime_4439_);
lean_inc(v_trace_4438_);
lean_inc(v_log_4435_);
lean_dec(v_a_4417_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4618_;
goto v_resetjp_4440_;
}
v___jp_4419_:
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_a_4420_);
lean_ctor_set(v___x_4422_, 1, v_a_4421_);
return v___x_4422_;
}
v___jp_4423_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4429_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4430_ = lean_array_get_size(v_log_4424_);
v___x_4431_ = lean_array_push(v_log_4424_, v___x_4429_);
v___x_4432_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
lean_ctor_set(v___x_4432_, 1, v_trace_4427_);
lean_ctor_set(v___x_4432_, 2, v_buildTime_4428_);
lean_ctor_set_uint8(v___x_4432_, sizeof(void*)*3, v_action_4425_);
lean_ctor_set_uint8(v___x_4432_, sizeof(void*)*3 + 1, v_wantsRebuild_4426_);
v___x_4433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4430_);
lean_ctor_set(v___x_4433_, 1, v___x_4432_);
return v___x_4433_;
}
v_resetjp_4440_:
{
uint8_t v_noBuild_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_noBuild_4443_ = lean_ctor_get_uint8(v_toBuildConfig_4434_, sizeof(void*)*3 + 2);
v___x_4444_ = l_Lake_JobAction_merge(v_action_4436_, v_action_4412_);
v___x_4445_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4411_);
v___x_4446_ = l_System_FilePath_addExtension(v_traceFile_4411_, v___x_4445_);
if (v_noBuild_4443_ == 0)
{
lean_object* v___x_4447_; lean_object* v_a_4449_; lean_object* v_a_4450_; lean_object* v___x_4454_; 
v___x_4447_ = lean_io_mono_ms_now();
v___x_4454_ = l_Lake_removeFileIfExists(v_file_4404_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4456_; 
lean_dec_ref_known(v___x_4454_, 1);
lean_inc_ref(v_log_4435_);
if (v_isShared_4442_ == 0)
{
v___x_4456_ = v___x_4441_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_log_4435_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_trace_4438_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_buildTime_4439_);
lean_ctor_set_uint8(v_reuseFailAlloc_4593_, sizeof(void*)*3 + 1, v_wantsRebuild_4437_);
v___x_4456_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4457_; 
lean_ctor_set_uint8(v___x_4456_, sizeof(void*)*3, v___x_4444_);
lean_inc_ref(v_a_4416_);
lean_inc(v_a_4415_);
lean_inc(v_a_4414_);
lean_inc(v_a_4413_);
v___x_4457_ = lean_apply_7(v_build_4405_, v_a_4409_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v___x_4456_, lean_box(0));
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v_log_4459_; uint8_t v_action_4460_; uint8_t v_wantsRebuild_4461_; lean_object* v_trace_4462_; lean_object* v_buildTime_4463_; lean_object* v___x_4464_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 1);
lean_inc(v_a_4458_);
lean_dec_ref_known(v___x_4457_, 2);
v_log_4459_ = lean_ctor_get(v_a_4458_, 0);
v_action_4460_ = lean_ctor_get_uint8(v_a_4458_, sizeof(void*)*3);
v_wantsRebuild_4461_ = lean_ctor_get_uint8(v_a_4458_, sizeof(void*)*3 + 1);
v_trace_4462_ = lean_ctor_get(v_a_4458_, 1);
v_buildTime_4463_ = lean_ctor_get(v_a_4458_, 2);
lean_inc_ref(v_file_4404_);
v___x_4464_ = l_Lake_clearFileHash(v_file_4404_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v___x_4465_; 
lean_dec_ref_known(v___x_4464_, 1);
v___x_4465_ = l_Lake_removeFileIfExists(v_traceFile_4406_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4557_; 
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4557_ == 0)
{
lean_object* v_unused_4558_; 
v_unused_4558_ = lean_ctor_get(v___x_4465_, 0);
lean_dec(v_unused_4558_);
v___x_4467_ = v___x_4465_;
v_isShared_4468_ = v_isSharedCheck_4557_;
goto v_resetjp_4466_;
}
else
{
lean_dec(v___x_4465_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4557_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lake_computeArtifact___redArg(v_file_4404_, v_ext_4407_, v_text_4408_, v_a_4416_, v_a_4458_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v_a_4471_; lean_object* v_descr_4472_; lean_object* v_log_4473_; uint8_t v_action_4474_; uint8_t v_wantsRebuild_4475_; lean_object* v_trace_4476_; lean_object* v_buildTime_4477_; uint64_t v_hash_4478_; lean_object* v_ext_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___y_4484_; lean_object* v___x_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 1);
lean_inc(v_a_4470_);
v_a_4471_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v___x_4469_, 2);
v_descr_4472_ = lean_ctor_get(v_a_4471_, 0);
v_log_4473_ = lean_ctor_get(v_a_4470_, 0);
v_action_4474_ = lean_ctor_get_uint8(v_a_4470_, sizeof(void*)*3);
v_wantsRebuild_4475_ = lean_ctor_get_uint8(v_a_4470_, sizeof(void*)*3 + 1);
v_trace_4476_ = lean_ctor_get(v_a_4470_, 1);
v_buildTime_4477_ = lean_ctor_get(v_a_4470_, 2);
v_hash_4478_ = lean_ctor_get_uint64(v_descr_4472_, sizeof(void*)*1);
v_ext_4479_ = lean_ctor_get(v_descr_4472_, 0);
v___x_4480_ = lean_array_get_size(v_log_4435_);
lean_dec_ref(v_log_4435_);
v___x_4481_ = lean_array_get_size(v_log_4473_);
v___x_4482_ = l_Array_extract___redArg(v_log_4473_, v___x_4480_, v___x_4481_);
v___x_4547_ = lean_string_utf8_byte_size(v_ext_4479_);
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = lean_nat_dec_eq(v___x_4547_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4550_ = l_Lake_lowerHexUInt64(v_hash_4478_);
v___x_4551_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4552_ = lean_string_append(v___x_4550_, v___x_4551_);
v___x_4553_ = lean_string_append(v___x_4552_, v_ext_4479_);
v___y_4484_ = v___x_4553_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lake_lowerHexUInt64(v_hash_4478_);
v___y_4484_ = v___x_4554_;
goto v___jp_4483_;
}
v___jp_4483_:
{
lean_object* v___x_4486_; 
if (v_isShared_4468_ == 0)
{
lean_ctor_set_tag(v___x_4467_, 3);
lean_ctor_set(v___x_4467_, 0, v___y_4484_);
v___x_4486_ = v___x_4467_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___y_4484_);
v___x_4486_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4410_, v___x_4486_, v___x_4482_);
v___x_4488_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4411_, v___x_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4529_; 
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; 
v_unused_4530_ = lean_ctor_get(v___x_4488_, 0);
lean_dec(v_unused_4530_);
v___x_4490_ = v___x_4488_;
v_isShared_4491_ = v_isSharedCheck_4529_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v___x_4488_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4529_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lake_removeFileIfExists(v___x_4446_);
lean_dec_ref(v___x_4446_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4512_; 
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; 
v_unused_4513_ = lean_ctor_get(v___x_4492_, 0);
lean_dec(v_unused_4513_);
v___x_4494_ = v___x_4492_;
v_isShared_4495_ = v_isSharedCheck_4512_;
goto v_resetjp_4493_;
}
else
{
lean_dec(v___x_4492_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4512_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
lean_inc(v_a_4471_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v_a_4471_);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4471_);
v___x_4497_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4499_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 1);
lean_ctor_set(v___x_4490_, 0, v___x_4497_);
v___x_4499_ = v___x_4490_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4497_);
v___x_4499_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4500_; lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
v___x_4500_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4447_, v___x_4499_, v_a_4470_);
lean_dec_ref(v___x_4499_);
lean_dec(v___x_4447_);
v_a_4501_ = lean_ctor_get(v___x_4500_, 1);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v___x_4500_, 0);
lean_dec(v_unused_4509_);
v___x_4503_ = v___x_4500_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4500_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v_a_4471_);
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4471_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
}
else
{
lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4525_; 
lean_inc(v_buildTime_4477_);
lean_inc_ref(v_trace_4476_);
lean_inc_ref(v_log_4473_);
lean_del_object(v___x_4490_);
lean_dec(v_a_4471_);
v_isSharedCheck_4525_ = !lean_is_exclusive(v_a_4470_);
if (v_isSharedCheck_4525_ == 0)
{
lean_object* v_unused_4526_; lean_object* v_unused_4527_; lean_object* v_unused_4528_; 
v_unused_4526_ = lean_ctor_get(v_a_4470_, 2);
lean_dec(v_unused_4526_);
v_unused_4527_ = lean_ctor_get(v_a_4470_, 1);
lean_dec(v_unused_4527_);
v_unused_4528_ = lean_ctor_get(v_a_4470_, 0);
lean_dec(v_unused_4528_);
v___x_4515_ = v_a_4470_;
v_isShared_4516_ = v_isSharedCheck_4525_;
goto v_resetjp_4514_;
}
else
{
lean_dec(v_a_4470_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4525_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v_a_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
v_a_4517_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4492_, 1);
v___x_4518_ = lean_io_error_to_string(v_a_4517_);
v___x_4519_ = 3;
v___x_4520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4520_, 0, v___x_4518_);
lean_ctor_set_uint8(v___x_4520_, sizeof(void*)*1, v___x_4519_);
v___x_4521_ = lean_array_push(v_log_4473_, v___x_4520_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4521_);
v___x_4523_ = v___x_4515_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_trace_4476_);
lean_ctor_set(v_reuseFailAlloc_4524_, 2, v_buildTime_4477_);
lean_ctor_set_uint8(v_reuseFailAlloc_4524_, sizeof(void*)*3, v_action_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4524_, sizeof(void*)*3 + 1, v_wantsRebuild_4475_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
v_a_4449_ = v___x_4481_;
v_a_4450_ = v___x_4523_;
goto v___jp_4448_;
}
}
}
}
}
else
{
lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4542_; 
lean_inc(v_buildTime_4477_);
lean_inc_ref(v_trace_4476_);
lean_inc_ref(v_log_4473_);
lean_dec(v_a_4471_);
lean_dec_ref(v___x_4446_);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_a_4470_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; lean_object* v_unused_4544_; lean_object* v_unused_4545_; 
v_unused_4543_ = lean_ctor_get(v_a_4470_, 2);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_a_4470_, 1);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_a_4470_, 0);
lean_dec(v_unused_4545_);
v___x_4532_ = v_a_4470_;
v_isShared_4533_ = v_isSharedCheck_4542_;
goto v_resetjp_4531_;
}
else
{
lean_dec(v_a_4470_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4542_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_a_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4540_; 
v_a_4534_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4535_ = lean_io_error_to_string(v_a_4534_);
v___x_4536_ = 3;
v___x_4537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4537_, 0, v___x_4535_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*1, v___x_4536_);
v___x_4538_ = lean_array_push(v_log_4473_, v___x_4537_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4538_);
v___x_4540_ = v___x_4532_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_trace_4476_);
lean_ctor_set(v_reuseFailAlloc_4541_, 2, v_buildTime_4477_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*3, v_action_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*3 + 1, v_wantsRebuild_4475_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
v_a_4449_ = v___x_4481_;
v_a_4450_ = v___x_4540_;
goto v___jp_4448_;
}
}
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v_a_4556_; 
lean_del_object(v___x_4467_);
lean_dec_ref(v___x_4446_);
lean_dec_ref(v_log_4435_);
lean_dec_ref(v_traceFile_4411_);
v_a_4555_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4555_);
v_a_4556_ = lean_ctor_get(v___x_4469_, 1);
lean_inc(v_a_4556_);
lean_dec_ref_known(v___x_4469_, 2);
v_a_4449_ = v_a_4555_;
v_a_4450_ = v_a_4556_;
goto v___jp_4448_;
}
}
}
else
{
lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4571_; 
lean_inc(v_buildTime_4463_);
lean_inc_ref(v_trace_4462_);
lean_inc_ref(v_log_4459_);
lean_dec_ref(v___x_4446_);
lean_dec_ref(v_log_4435_);
lean_dec_ref(v_traceFile_4411_);
lean_dec_ref(v_ext_4407_);
lean_dec_ref(v_file_4404_);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_a_4458_);
if (v_isSharedCheck_4571_ == 0)
{
lean_object* v_unused_4572_; lean_object* v_unused_4573_; lean_object* v_unused_4574_; 
v_unused_4572_ = lean_ctor_get(v_a_4458_, 2);
lean_dec(v_unused_4572_);
v_unused_4573_ = lean_ctor_get(v_a_4458_, 1);
lean_dec(v_unused_4573_);
v_unused_4574_ = lean_ctor_get(v_a_4458_, 0);
lean_dec(v_unused_4574_);
v___x_4560_ = v_a_4458_;
v_isShared_4561_ = v_isSharedCheck_4571_;
goto v_resetjp_4559_;
}
else
{
lean_dec(v_a_4458_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4571_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v_a_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
v_a_4562_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4563_ = lean_io_error_to_string(v_a_4562_);
v___x_4564_ = 3;
v___x_4565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*1, v___x_4564_);
v___x_4566_ = lean_array_get_size(v_log_4459_);
v___x_4567_ = lean_array_push(v_log_4459_, v___x_4565_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4567_);
v___x_4569_ = v___x_4560_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_trace_4462_);
lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_buildTime_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4570_, sizeof(void*)*3, v_action_4460_);
lean_ctor_set_uint8(v_reuseFailAlloc_4570_, sizeof(void*)*3 + 1, v_wantsRebuild_4461_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
v_a_4449_ = v___x_4566_;
v_a_4450_ = v___x_4569_;
goto v___jp_4448_;
}
}
}
}
else
{
lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4587_; 
lean_inc(v_buildTime_4463_);
lean_inc_ref(v_trace_4462_);
lean_inc_ref(v_log_4459_);
lean_dec_ref(v___x_4446_);
lean_dec_ref(v_log_4435_);
lean_dec_ref(v_traceFile_4411_);
lean_dec_ref(v_ext_4407_);
lean_dec_ref(v_file_4404_);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_a_4458_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; lean_object* v_unused_4589_; lean_object* v_unused_4590_; 
v_unused_4588_ = lean_ctor_get(v_a_4458_, 2);
lean_dec(v_unused_4588_);
v_unused_4589_ = lean_ctor_get(v_a_4458_, 1);
lean_dec(v_unused_4589_);
v_unused_4590_ = lean_ctor_get(v_a_4458_, 0);
lean_dec(v_unused_4590_);
v___x_4576_ = v_a_4458_;
v_isShared_4577_ = v_isSharedCheck_4587_;
goto v_resetjp_4575_;
}
else
{
lean_dec(v_a_4458_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4587_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_a_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
v_a_4578_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v___x_4464_, 1);
v___x_4579_ = lean_io_error_to_string(v_a_4578_);
v___x_4580_ = 3;
v___x_4581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4581_, 0, v___x_4579_);
lean_ctor_set_uint8(v___x_4581_, sizeof(void*)*1, v___x_4580_);
v___x_4582_ = lean_array_get_size(v_log_4459_);
v___x_4583_ = lean_array_push(v_log_4459_, v___x_4581_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4583_);
v___x_4585_ = v___x_4576_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_trace_4462_);
lean_ctor_set(v_reuseFailAlloc_4586_, 2, v_buildTime_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4586_, sizeof(void*)*3, v_action_4460_);
lean_ctor_set_uint8(v_reuseFailAlloc_4586_, sizeof(void*)*3 + 1, v_wantsRebuild_4461_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
v_a_4449_ = v___x_4582_;
v_a_4450_ = v___x_4585_;
goto v___jp_4448_;
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v_a_4592_; 
lean_dec_ref(v___x_4446_);
lean_dec_ref(v_log_4435_);
lean_dec_ref(v_traceFile_4411_);
lean_dec_ref(v_ext_4407_);
lean_dec_ref(v_file_4404_);
v_a_4591_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4591_);
v_a_4592_ = lean_ctor_get(v___x_4457_, 1);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4457_, 2);
v_a_4449_ = v_a_4591_;
v_a_4450_ = v_a_4592_;
goto v___jp_4448_;
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
lean_dec_ref(v___x_4446_);
lean_dec_ref(v_traceFile_4411_);
lean_dec_ref(v_a_4409_);
lean_dec_ref(v_ext_4407_);
lean_dec_ref(v_build_4405_);
lean_dec_ref(v_file_4404_);
v_a_4594_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4454_, 1);
v___x_4595_ = lean_io_error_to_string(v_a_4594_);
v___x_4596_ = 3;
v___x_4597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4597_, 0, v___x_4595_);
lean_ctor_set_uint8(v___x_4597_, sizeof(void*)*1, v___x_4596_);
v___x_4598_ = lean_array_get_size(v_log_4435_);
v___x_4599_ = lean_array_push(v_log_4435_, v___x_4597_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4599_);
v___x_4601_ = v___x_4441_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_trace_4438_);
lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_buildTime_4439_);
lean_ctor_set_uint8(v_reuseFailAlloc_4602_, sizeof(void*)*3 + 1, v_wantsRebuild_4437_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
lean_ctor_set_uint8(v___x_4601_, sizeof(void*)*3, v___x_4444_);
v_a_4449_ = v___x_4598_;
v_a_4450_ = v___x_4601_;
goto v___jp_4448_;
}
}
v___jp_4448_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_a_4453_; 
v___x_4451_ = lean_box(0);
v___x_4452_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4447_, v___x_4451_, v_a_4450_);
lean_dec(v___x_4447_);
v_a_4453_ = lean_ctor_get(v___x_4452_, 1);
lean_inc(v_a_4453_);
lean_dec_ref(v___x_4452_);
v_a_4420_ = v_a_4449_;
v_a_4421_ = v_a_4453_;
goto v___jp_4419_;
}
}
else
{
uint8_t v___x_4603_; 
lean_dec_ref(v_a_4409_);
lean_dec_ref(v_ext_4407_);
lean_dec_ref(v_build_4405_);
lean_dec_ref(v_file_4404_);
v___x_4603_ = l_System_FilePath_pathExists(v_traceFile_4411_);
lean_dec_ref(v_traceFile_4411_);
if (v___x_4603_ == 0)
{
lean_dec_ref(v___x_4446_);
lean_del_object(v___x_4441_);
v_log_4424_ = v_log_4435_;
v_action_4425_ = v___x_4444_;
v_wantsRebuild_4426_ = v_noBuild_4443_;
v_trace_4427_ = v_trace_4438_;
v_buildTime_4428_ = v_buildTime_4439_;
goto v___jp_4423_;
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4604_ = lean_box(0);
v___x_4605_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4606_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4410_, v___x_4604_, v___x_4605_);
v___x_4607_ = l_Lake_BuildMetadata_writeFile(v___x_4446_, v___x_4606_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_dec_ref_known(v___x_4607_, 1);
lean_del_object(v___x_4441_);
v_log_4424_ = v_log_4435_;
v_action_4425_ = v___x_4444_;
v_wantsRebuild_4426_ = v_noBuild_4443_;
v_trace_4427_ = v_trace_4438_;
v_buildTime_4428_ = v_buildTime_4439_;
goto v___jp_4423_;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4609_; uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4607_, 1);
v___x_4609_ = lean_io_error_to_string(v_a_4608_);
v___x_4610_ = 3;
v___x_4611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set_uint8(v___x_4611_, sizeof(void*)*1, v___x_4610_);
v___x_4612_ = lean_array_get_size(v_log_4435_);
v___x_4613_ = lean_array_push(v_log_4435_, v___x_4611_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4613_);
v___x_4615_ = v___x_4441_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4613_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v_trace_4438_);
lean_ctor_set(v_reuseFailAlloc_4617_, 2, v_buildTime_4439_);
v___x_4615_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; 
lean_ctor_set_uint8(v___x_4615_, sizeof(void*)*3, v___x_4444_);
lean_ctor_set_uint8(v___x_4615_, sizeof(void*)*3 + 1, v_noBuild_4443_);
v___x_4616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4612_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
return v___x_4616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4619_, lean_object* v_build_4620_, lean_object* v_traceFile_4621_, lean_object* v_ext_4622_, lean_object* v_text_4623_, lean_object* v_a_4624_, lean_object* v_depTrace_4625_, lean_object* v_traceFile_4626_, lean_object* v_action_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
uint8_t v_text_boxed_4634_; uint8_t v_action_boxed_4635_; lean_object* v_res_4636_; 
v_text_boxed_4634_ = lean_unbox(v_text_4623_);
v_action_boxed_4635_ = lean_unbox(v_action_4627_);
v_res_4636_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4619_, v_build_4620_, v_traceFile_4621_, v_ext_4622_, v_text_boxed_4634_, v_a_4624_, v_depTrace_4625_, v_traceFile_4626_, v_action_boxed_4635_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_depTrace_4625_);
lean_dec_ref(v_traceFile_4621_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4637_, lean_object* v_build_4638_, uint8_t v_text_4639_, lean_object* v_ext_4640_, lean_object* v_depTrace_4641_, lean_object* v_traceFile_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_){
_start:
{
uint8_t v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = 5;
lean_inc_ref(v_traceFile_4642_);
v___x_4651_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4637_, v_build_4638_, v_traceFile_4642_, v_ext_4640_, v_text_4639_, v_a_4643_, v_depTrace_4641_, v_traceFile_4642_, v___x_4650_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_);
lean_dec_ref(v_traceFile_4642_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4652_, lean_object* v_build_4653_, lean_object* v_text_4654_, lean_object* v_ext_4655_, lean_object* v_depTrace_4656_, lean_object* v_traceFile_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
uint8_t v_text_boxed_4665_; lean_object* v_res_4666_; 
v_text_boxed_4665_ = lean_unbox(v_text_4654_);
v_res_4666_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4652_, v_build_4653_, v_text_boxed_4665_, v_ext_4655_, v_depTrace_4656_, v_traceFile_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec_ref(v_depTrace_4656_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4668_, lean_object* v_traceFile_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v_log_4672_; uint8_t v_action_4673_; uint8_t v_wantsRebuild_4674_; lean_object* v_trace_4675_; lean_object* v_buildTime_4676_; lean_object* v___x_4677_; 
v_log_4672_ = lean_ctor_get(v_a_4670_, 0);
v_action_4673_ = lean_ctor_get_uint8(v_a_4670_, sizeof(void*)*3);
v_wantsRebuild_4674_ = lean_ctor_get_uint8(v_a_4670_, sizeof(void*)*3 + 1);
v_trace_4675_ = lean_ctor_get(v_a_4670_, 1);
v_buildTime_4676_ = lean_ctor_get(v_a_4670_, 2);
v___x_4677_ = lean_io_metadata(v_traceFile_4669_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v_modified_4679_; lean_object* v_descr_4680_; lean_object* v_path_4681_; lean_object* v_name_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4690_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
v_modified_4679_ = lean_ctor_get(v_a_4678_, 1);
lean_inc_ref(v_modified_4679_);
lean_dec(v_a_4678_);
v_descr_4680_ = lean_ctor_get(v_art_4668_, 0);
v_path_4681_ = lean_ctor_get(v_art_4668_, 1);
v_name_4682_ = lean_ctor_get(v_art_4668_, 2);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_art_4668_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; 
v_unused_4691_ = lean_ctor_get(v_art_4668_, 3);
lean_dec(v_unused_4691_);
v___x_4684_ = v_art_4668_;
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_name_4682_);
lean_inc(v_path_4681_);
lean_inc(v_descr_4680_);
lean_dec(v_art_4668_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 3, v_modified_4679_);
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_descr_4680_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_path_4681_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_name_4682_);
lean_ctor_set(v_reuseFailAlloc_4689_, 3, v_modified_4679_);
v___x_4687_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
lean_ctor_set(v___x_4688_, 1, v_a_4670_);
return v___x_4688_;
}
}
}
else
{
lean_object* v_a_4692_; 
v_a_4692_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___x_4677_, 1);
if (lean_obj_tag(v_a_4692_) == 11)
{
lean_object* v___x_4693_; 
lean_dec_ref_known(v_a_4692_, 2);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v_art_4668_);
lean_ctor_set(v___x_4693_, 1, v_a_4670_);
return v___x_4693_;
}
else
{
lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4708_; 
lean_inc(v_buildTime_4676_);
lean_inc_ref(v_trace_4675_);
lean_inc_ref(v_log_4672_);
lean_dec_ref(v_art_4668_);
v_isSharedCheck_4708_ = !lean_is_exclusive(v_a_4670_);
if (v_isSharedCheck_4708_ == 0)
{
lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; 
v_unused_4709_ = lean_ctor_get(v_a_4670_, 2);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_a_4670_, 1);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_a_4670_, 0);
lean_dec(v_unused_4711_);
v___x_4695_ = v_a_4670_;
v_isShared_4696_ = v_isSharedCheck_4708_;
goto v_resetjp_4694_;
}
else
{
lean_dec(v_a_4670_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4708_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; uint8_t v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4697_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4698_ = lean_io_error_to_string(v_a_4692_);
v___x_4699_ = lean_string_append(v___x_4697_, v___x_4698_);
lean_dec_ref(v___x_4698_);
v___x_4700_ = 3;
v___x_4701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4701_, 0, v___x_4699_);
lean_ctor_set_uint8(v___x_4701_, sizeof(void*)*1, v___x_4700_);
v___x_4702_ = lean_array_get_size(v_log_4672_);
v___x_4703_ = lean_array_push(v_log_4672_, v___x_4701_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 0, v___x_4703_);
v___x_4705_ = v___x_4695_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4703_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v_trace_4675_);
lean_ctor_set(v_reuseFailAlloc_4707_, 2, v_buildTime_4676_);
lean_ctor_set_uint8(v_reuseFailAlloc_4707_, sizeof(void*)*3, v_action_4673_);
lean_ctor_set_uint8(v_reuseFailAlloc_4707_, sizeof(void*)*3 + 1, v_wantsRebuild_4674_);
v___x_4705_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4702_);
lean_ctor_set(v___x_4706_, 1, v___x_4705_);
return v___x_4706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4712_, lean_object* v_traceFile_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4712_, v_traceFile_4713_, v_a_4714_);
lean_dec_ref(v_traceFile_4713_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4717_, lean_object* v_traceFile_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4717_, v_traceFile_4718_, v_a_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4727_, lean_object* v_traceFile_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4727_, v_traceFile_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
lean_dec_ref(v_traceFile_4728_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4737_, lean_object* v_____r_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4746_, 0, v_a_4737_);
v___x_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4746_);
v___x_4748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v___y_4744_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4749_, lean_object* v_____r_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4749_, v_____r_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4759_, lean_object* v___y_4760_, uint64_t v_inputHash_4761_, lean_object* v_savedTrace_4762_, lean_object* v_pkg_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___y_4771_; lean_object* v_a_4775_; lean_object* v_a_4776_; lean_object* v___y_4791_; 
if (lean_obj_tag(v_savedTrace_4762_) == 2)
{
lean_object* v_data_4806_; uint64_t v_depHash_4807_; lean_object* v_outputs_x3f_4808_; uint8_t v___x_4809_; 
v_data_4806_ = lean_ctor_get(v_savedTrace_4762_, 0);
lean_inc_ref(v_data_4806_);
lean_dec_ref_known(v_savedTrace_4762_, 1);
v_depHash_4807_ = lean_ctor_get_uint64(v_data_4806_, sizeof(void*)*3);
v_outputs_x3f_4808_ = lean_ctor_get(v_data_4806_, 1);
lean_inc(v_outputs_x3f_4808_);
lean_dec_ref(v_data_4806_);
v___x_4809_ = lean_uint64_dec_eq(v_depHash_4807_, v_inputHash_4761_);
if (v___x_4809_ == 0)
{
lean_dec(v_outputs_x3f_4808_);
lean_dec_ref(v_pkg_4763_);
lean_dec_ref(v___y_4760_);
v___y_4771_ = v_a_4768_;
goto v___jp_4770_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4808_) == 1)
{
lean_object* v_val_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_val_4810_ = lean_ctor_get(v_outputs_x3f_4808_, 0);
lean_inc_n(v_val_4810_, 2);
lean_dec_ref_known(v_outputs_x3f_4808_, 1);
v___x_4811_ = lean_box(0);
v___x_4812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4812_, 0, v_val_4810_);
lean_ctor_set(v___x_4812_, 1, v___x_4811_);
lean_ctor_set(v___x_4812_, 2, v___x_4811_);
lean_inc_ref(v___y_4760_);
v___x_4813_ = l_Lake_resolveArtifactOutput(v___x_4812_, v_exe_4759_, v___y_4760_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_config_4814_; lean_object* v_a_4815_; lean_object* v_a_4816_; lean_object* v_enableArtifactCache_x3f_4817_; lean_object* v_a_4819_; uint8_t v_a_4823_; lean_object* v_a_4824_; 
v_config_4814_ = lean_ctor_get(v_pkg_4763_, 6);
v_a_4815_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4815_);
v_a_4816_ = lean_ctor_get(v___x_4813_, 1);
lean_inc(v_a_4816_);
lean_dec_ref_known(v___x_4813_, 2);
v_enableArtifactCache_x3f_4817_ = lean_ctor_get(v_config_4814_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4817_) == 0)
{
lean_object* v_toContext_4856_; lean_object* v_lakeEnv_4857_; lean_object* v_enableArtifactCache_x3f_4858_; 
v_toContext_4856_ = lean_ctor_get(v_a_4767_, 1);
v_lakeEnv_4857_ = lean_ctor_get(v_toContext_4856_, 0);
v_enableArtifactCache_x3f_4858_ = lean_ctor_get(v_lakeEnv_4857_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4858_) == 0)
{
lean_object* v_packages_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v_config_4862_; lean_object* v_enableArtifactCache_x3f_4863_; 
v_packages_4859_ = lean_ctor_get(v_toContext_4856_, 4);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = lean_array_fget_borrowed(v_packages_4859_, v___x_4860_);
v_config_4862_ = lean_ctor_get(v___x_4861_, 6);
v_enableArtifactCache_x3f_4863_ = lean_ctor_get(v_config_4862_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4863_) == 0)
{
lean_dec(v_val_4810_);
lean_dec_ref(v_pkg_4763_);
v_a_4819_ = v_a_4816_;
goto v___jp_4818_;
}
else
{
lean_object* v_val_4864_; uint8_t v___x_4865_; 
v_val_4864_ = lean_ctor_get(v_enableArtifactCache_x3f_4863_, 0);
v___x_4865_ = lean_unbox(v_val_4864_);
v_a_4823_ = v___x_4865_;
v_a_4824_ = v_a_4816_;
goto v___jp_4822_;
}
}
else
{
lean_object* v_val_4866_; uint8_t v___x_4867_; 
v_val_4866_ = lean_ctor_get(v_enableArtifactCache_x3f_4858_, 0);
v___x_4867_ = lean_unbox(v_val_4866_);
v_a_4823_ = v___x_4867_;
v_a_4824_ = v_a_4816_;
goto v___jp_4822_;
}
}
else
{
lean_object* v_val_4868_; uint8_t v___x_4869_; 
v_val_4868_ = lean_ctor_get(v_enableArtifactCache_x3f_4817_, 0);
v___x_4869_ = lean_unbox(v_val_4868_);
v_a_4823_ = v___x_4869_;
v_a_4824_ = v_a_4816_;
goto v___jp_4822_;
}
v___jp_4818_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = lean_box(0);
v___x_4821_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4815_, v___x_4820_, v___y_4760_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4819_);
lean_dec_ref(v___y_4760_);
v___y_4791_ = v___x_4821_;
goto v___jp_4790_;
}
v___jp_4822_:
{
if (v_a_4823_ == 0)
{
lean_dec(v_val_4810_);
lean_dec_ref(v_pkg_4763_);
v_a_4819_ = v_a_4824_;
goto v___jp_4818_;
}
else
{
lean_object* v_toContext_4825_; lean_object* v_log_4826_; uint8_t v_action_4827_; uint8_t v_wantsRebuild_4828_; lean_object* v_trace_4829_; lean_object* v_buildTime_4830_; lean_object* v_lakeCache_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; lean_object* v___x_4834_; 
v_toContext_4825_ = lean_ctor_get(v_a_4767_, 1);
v_log_4826_ = lean_ctor_get(v_a_4824_, 0);
v_action_4827_ = lean_ctor_get_uint8(v_a_4824_, sizeof(void*)*3);
v_wantsRebuild_4828_ = lean_ctor_get_uint8(v_a_4824_, sizeof(void*)*3 + 1);
v_trace_4829_ = lean_ctor_get(v_a_4824_, 1);
v_buildTime_4830_ = lean_ctor_get(v_a_4824_, 2);
v_lakeCache_4831_ = lean_ctor_get(v_toContext_4825_, 2);
v___x_4832_ = l_Lake_Package_cacheScope(v_pkg_4763_);
v___x_4833_ = 0;
lean_inc_ref(v_lakeCache_4831_);
v___x_4834_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4831_, v___x_4832_, v_inputHash_4761_, v_val_4810_, v___x_4811_, v___x_4811_, v___x_4833_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_dec_ref_known(v___x_4834_, 1);
v___x_4835_ = lean_box(0);
v___x_4836_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4815_, v___x_4835_, v___y_4760_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4824_);
lean_dec_ref(v___y_4760_);
v___y_4791_ = v___x_4836_;
goto v___jp_4790_;
}
else
{
lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4852_; 
lean_inc(v_buildTime_4830_);
lean_inc_ref(v_trace_4829_);
lean_inc_ref(v_log_4826_);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_a_4824_);
if (v_isSharedCheck_4852_ == 0)
{
lean_object* v_unused_4853_; lean_object* v_unused_4854_; lean_object* v_unused_4855_; 
v_unused_4853_ = lean_ctor_get(v_a_4824_, 2);
lean_dec(v_unused_4853_);
v_unused_4854_ = lean_ctor_get(v_a_4824_, 1);
lean_dec(v_unused_4854_);
v_unused_4855_ = lean_ctor_get(v_a_4824_, 0);
lean_dec(v_unused_4855_);
v___x_4838_ = v_a_4824_;
v_isShared_4839_ = v_isSharedCheck_4852_;
goto v_resetjp_4837_;
}
else
{
lean_dec(v_a_4824_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4852_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v_a_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v_a_4840_ = lean_ctor_get(v___x_4834_, 0);
lean_inc(v_a_4840_);
lean_dec_ref_known(v___x_4834_, 1);
v___x_4841_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4842_ = lean_io_error_to_string(v_a_4840_);
v___x_4843_ = lean_string_append(v___x_4841_, v___x_4842_);
lean_dec_ref(v___x_4842_);
v___x_4844_ = 2;
v___x_4845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4845_, 0, v___x_4843_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1, v___x_4844_);
v___x_4846_ = lean_box(0);
v___x_4847_ = lean_array_push(v_log_4826_, v___x_4845_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4847_);
v___x_4849_ = v___x_4838_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4847_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_trace_4829_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_buildTime_4830_);
lean_ctor_set_uint8(v_reuseFailAlloc_4851_, sizeof(void*)*3, v_action_4827_);
lean_ctor_set_uint8(v_reuseFailAlloc_4851_, sizeof(void*)*3 + 1, v_wantsRebuild_4828_);
v___x_4849_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4815_, v___x_4846_, v___y_4760_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v___x_4849_);
lean_dec_ref(v___y_4760_);
v___y_4791_ = v___x_4850_;
goto v___jp_4790_;
}
}
}
}
}
}
else
{
lean_object* v_a_4870_; lean_object* v_a_4871_; 
lean_dec(v_val_4810_);
lean_dec_ref(v_pkg_4763_);
lean_dec_ref(v___y_4760_);
v_a_4870_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4870_);
v_a_4871_ = lean_ctor_get(v___x_4813_, 1);
lean_inc(v_a_4871_);
lean_dec_ref_known(v___x_4813_, 2);
v_a_4775_ = v_a_4870_;
v_a_4776_ = v_a_4871_;
goto v___jp_4774_;
}
}
else
{
lean_dec(v_outputs_x3f_4808_);
lean_dec_ref(v_pkg_4763_);
lean_dec_ref(v___y_4760_);
v___y_4771_ = v_a_4768_;
goto v___jp_4770_;
}
}
}
else
{
lean_dec_ref(v_pkg_4763_);
lean_dec(v_savedTrace_4762_);
lean_dec_ref(v___y_4760_);
v___y_4771_ = v_a_4768_;
goto v___jp_4770_;
}
v___jp_4770_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = lean_box(0);
v___x_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
lean_ctor_set(v___x_4773_, 1, v___y_4771_);
return v___x_4773_;
}
v___jp_4774_:
{
lean_object* v_log_4777_; uint8_t v_action_4778_; uint8_t v_wantsRebuild_4779_; lean_object* v_trace_4780_; lean_object* v_buildTime_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4789_; 
v_log_4777_ = lean_ctor_get(v_a_4776_, 0);
v_action_4778_ = lean_ctor_get_uint8(v_a_4776_, sizeof(void*)*3);
v_wantsRebuild_4779_ = lean_ctor_get_uint8(v_a_4776_, sizeof(void*)*3 + 1);
v_trace_4780_ = lean_ctor_get(v_a_4776_, 1);
v_buildTime_4781_ = lean_ctor_get(v_a_4776_, 2);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_a_4776_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4783_ = v_a_4776_;
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_buildTime_4781_);
lean_inc(v_trace_4780_);
lean_inc(v_log_4777_);
lean_dec(v_a_4776_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4785_; lean_object* v___x_4787_; 
v___x_4785_ = l_Array_shrink___redArg(v_log_4777_, v_a_4775_);
lean_dec(v_a_4775_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4785_);
v___x_4787_ = v___x_4783_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_trace_4780_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_buildTime_4781_);
lean_ctor_set_uint8(v_reuseFailAlloc_4788_, sizeof(void*)*3, v_action_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4788_, sizeof(void*)*3 + 1, v_wantsRebuild_4779_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
v___y_4771_ = v___x_4787_;
goto v___jp_4770_;
}
}
}
v___jp_4790_:
{
if (lean_obj_tag(v___y_4791_) == 0)
{
lean_object* v_a_4792_; 
v_a_4792_ = lean_ctor_get(v___y_4791_, 0);
if (lean_obj_tag(v_a_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4801_; 
lean_inc_ref(v_a_4792_);
v_a_4793_ = lean_ctor_get(v___y_4791_, 1);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___y_4791_);
if (v_isSharedCheck_4801_ == 0)
{
lean_object* v_unused_4802_; 
v_unused_4802_ = lean_ctor_get(v___y_4791_, 0);
lean_dec(v_unused_4802_);
v___x_4795_ = v___y_4791_;
v_isShared_4796_ = v_isSharedCheck_4801_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___y_4791_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4801_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v_a_4797_; lean_object* v___x_4799_; 
v_a_4797_ = lean_ctor_get(v_a_4792_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v_a_4792_, 1);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v_a_4797_);
v___x_4799_ = v___x_4795_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4797_);
lean_ctor_set(v_reuseFailAlloc_4800_, 1, v_a_4793_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
lean_object* v_a_4803_; 
v_a_4803_ = lean_ctor_get(v___y_4791_, 1);
lean_inc(v_a_4803_);
lean_dec_ref_known(v___y_4791_, 2);
v___y_4771_ = v_a_4803_;
goto v___jp_4770_;
}
}
else
{
lean_object* v_a_4804_; lean_object* v_a_4805_; 
v_a_4804_ = lean_ctor_get(v___y_4791_, 0);
lean_inc(v_a_4804_);
v_a_4805_ = lean_ctor_get(v___y_4791_, 1);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___y_4791_, 2);
v_a_4775_ = v_a_4804_;
v_a_4776_ = v_a_4805_;
goto v___jp_4774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4872_, lean_object* v___y_4873_, lean_object* v_inputHash_4874_, lean_object* v_savedTrace_4875_, lean_object* v_pkg_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
uint8_t v_exe_boxed_4883_; uint64_t v_inputHash_boxed_4884_; lean_object* v_res_4885_; 
v_exe_boxed_4883_ = lean_unbox(v_exe_4872_);
v_inputHash_boxed_4884_ = lean_unbox_uint64(v_inputHash_4874_);
lean_dec_ref(v_inputHash_4874_);
v_res_4885_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4883_, v___y_4873_, v_inputHash_boxed_4884_, v_savedTrace_4875_, v_pkg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec(v_a_4877_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4886_, size_t v_i_4887_, size_t v_stop_4888_, lean_object* v_b_4889_){
_start:
{
uint8_t v___x_4890_; 
v___x_4890_ = lean_usize_dec_eq(v_i_4887_, v_stop_4888_);
if (v___x_4890_ == 0)
{
lean_object* v___x_4891_; lean_object* v_message_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; size_t v___x_4896_; size_t v___x_4897_; 
v___x_4891_ = lean_array_uget_borrowed(v_as_4886_, v_i_4887_);
v_message_4892_ = lean_ctor_get(v___x_4891_, 0);
v___x_4893_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4894_ = lean_string_append(v_b_4889_, v___x_4893_);
v___x_4895_ = lean_string_append(v___x_4894_, v_message_4892_);
v___x_4896_ = ((size_t)1ULL);
v___x_4897_ = lean_usize_add(v_i_4887_, v___x_4896_);
v_i_4887_ = v___x_4897_;
v_b_4889_ = v___x_4895_;
goto _start;
}
else
{
return v_b_4889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4899_, lean_object* v_i_4900_, lean_object* v_stop_4901_, lean_object* v_b_4902_){
_start:
{
size_t v_i_boxed_4903_; size_t v_stop_boxed_4904_; lean_object* v_res_4905_; 
v_i_boxed_4903_ = lean_unbox_usize(v_i_4900_);
lean_dec(v_i_4900_);
v_stop_boxed_4904_ = lean_unbox_usize(v_stop_4901_);
lean_dec(v_stop_4901_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4899_, v_i_boxed_4903_, v_stop_boxed_4904_, v_b_4902_);
lean_dec_ref(v_as_4899_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4906_, lean_object* v___y_4907_, uint64_t v_inputHash_4908_, lean_object* v_pkg_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v_toContext_4916_; lean_object* v_log_4917_; uint8_t v_action_4918_; uint8_t v_wantsRebuild_4919_; lean_object* v_trace_4920_; lean_object* v_buildTime_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_5014_; 
v_toContext_4916_ = lean_ctor_get(v_a_4913_, 1);
v_log_4917_ = lean_ctor_get(v_a_4914_, 0);
v_action_4918_ = lean_ctor_get_uint8(v_a_4914_, sizeof(void*)*3);
v_wantsRebuild_4919_ = lean_ctor_get_uint8(v_a_4914_, sizeof(void*)*3 + 1);
v_trace_4920_ = lean_ctor_get(v_a_4914_, 1);
v_buildTime_4921_ = lean_ctor_get(v_a_4914_, 2);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_a_4914_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_4923_ = v_a_4914_;
v_isShared_4924_ = v_isSharedCheck_5014_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_buildTime_4921_);
lean_inc(v_trace_4920_);
lean_inc(v_log_4917_);
lean_dec(v_a_4914_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_5014_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v_lakeCache_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_lakeCache_4925_ = lean_ctor_get(v_toContext_4916_, 2);
v___x_4926_ = l_Lake_Package_cacheScope(v_pkg_4909_);
lean_inc_ref(v_lakeCache_4925_);
v___x_4927_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4925_, v___x_4926_, v_inputHash_4908_, v_log_4917_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_5001_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_a_4929_ = lean_ctor_get(v___x_4927_, 1);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4931_ = v___x_4927_;
v_isShared_4932_ = v_isSharedCheck_5001_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_5001_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v_a_4929_);
v___x_4934_ = v___x_4923_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4929_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v_trace_4920_);
lean_ctor_set(v_reuseFailAlloc_5000_, 2, v_buildTime_4921_);
lean_ctor_set_uint8(v_reuseFailAlloc_5000_, sizeof(void*)*3, v_action_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_5000_, sizeof(void*)*3 + 1, v_wantsRebuild_4919_);
v___x_4934_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
if (lean_obj_tag(v_a_4928_) == 1)
{
lean_object* v_val_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4995_; 
v_val_4935_ = lean_ctor_get(v_a_4928_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v_a_4928_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4937_ = v_a_4928_;
v_isShared_4938_ = v_isSharedCheck_4995_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_val_4935_);
lean_dec(v_a_4928_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4995_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4939_; lean_object* v_r_4941_; lean_object* v___y_4942_; 
v___x_4939_ = l_Lake_resolveArtifactOutput(v_val_4935_, v_exe_4906_, v___y_4907_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v___x_4934_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4946_; lean_object* v_a_4947_; lean_object* v___x_4949_; 
v_a_4946_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4946_);
v_a_4947_ = lean_ctor_get(v___x_4939_, 1);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4939_, 2);
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v_a_4946_);
v___x_4949_ = v___x_4937_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4946_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
v_r_4941_ = v___x_4949_;
v___y_4942_ = v_a_4947_;
goto v___jp_4940_;
}
}
else
{
lean_object* v_a_4951_; lean_object* v_a_4952_; lean_object* v_log_4953_; uint8_t v_action_4954_; uint8_t v_wantsRebuild_4955_; lean_object* v_trace_4956_; lean_object* v_buildTime_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4994_; 
lean_del_object(v___x_4937_);
v_a_4951_ = lean_ctor_get(v___x_4939_, 1);
lean_inc(v_a_4951_);
v_a_4952_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4952_);
lean_dec_ref_known(v___x_4939_, 2);
v_log_4953_ = lean_ctor_get(v_a_4951_, 0);
v_action_4954_ = lean_ctor_get_uint8(v_a_4951_, sizeof(void*)*3);
v_wantsRebuild_4955_ = lean_ctor_get_uint8(v_a_4951_, sizeof(void*)*3 + 1);
v_trace_4956_ = lean_ctor_get(v_a_4951_, 1);
v_buildTime_4957_ = lean_ctor_get(v_a_4951_, 2);
v_isSharedCheck_4994_ = !lean_is_exclusive(v_a_4951_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4959_ = v_a_4951_;
v_isShared_4960_ = v_isSharedCheck_4994_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_buildTime_4957_);
lean_inc(v_trace_4956_);
lean_inc(v_log_4953_);
lean_dec(v_a_4951_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4994_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___y_4965_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; 
v___x_4961_ = lean_array_get_size(v_log_4953_);
lean_inc(v_a_4952_);
v___x_4962_ = l_Array_extract___redArg(v_log_4953_, v_a_4952_, v___x_4961_);
v___x_4963_ = l_Array_shrink___redArg(v_log_4953_, v_a_4952_);
lean_dec(v_a_4952_);
v___x_4973_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4974_ = l_Lake_lowerHexUInt64(v_inputHash_4908_);
v___x_4975_ = lean_unsigned_to_nat(7u);
v___x_4976_ = lean_unsigned_to_nat(0u);
v___x_4977_ = lean_string_utf8_byte_size(v___x_4974_);
lean_inc_ref(v___x_4974_);
v___x_4978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4974_);
lean_ctor_set(v___x_4978_, 1, v___x_4976_);
lean_ctor_set(v___x_4978_, 2, v___x_4977_);
v___x_4979_ = l_String_Slice_Pos_nextn(v___x_4978_, v___x_4976_, v___x_4975_);
lean_dec_ref_known(v___x_4978_, 3);
v___x_4980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4974_);
lean_ctor_set(v___x_4980_, 1, v___x_4976_);
lean_ctor_set(v___x_4980_, 2, v___x_4979_);
v___x_4981_ = l_String_Slice_toString(v___x_4980_);
lean_dec_ref_known(v___x_4980_, 3);
v___x_4982_ = lean_string_append(v___x_4973_, v___x_4981_);
lean_dec_ref(v___x_4981_);
v___x_4983_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4984_ = lean_string_append(v___x_4982_, v___x_4983_);
v___x_4985_ = lean_array_get_size(v___x_4962_);
v___x_4986_ = lean_nat_dec_lt(v___x_4976_, v___x_4985_);
if (v___x_4986_ == 0)
{
lean_dec_ref(v___x_4962_);
v___y_4965_ = v___x_4984_;
goto v___jp_4964_;
}
else
{
uint8_t v___x_4987_; 
v___x_4987_ = lean_nat_dec_le(v___x_4985_, v___x_4985_);
if (v___x_4987_ == 0)
{
if (v___x_4986_ == 0)
{
lean_dec_ref(v___x_4962_);
v___y_4965_ = v___x_4984_;
goto v___jp_4964_;
}
else
{
size_t v___x_4988_; size_t v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = ((size_t)0ULL);
v___x_4989_ = lean_usize_of_nat(v___x_4985_);
v___x_4990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4962_, v___x_4988_, v___x_4989_, v___x_4984_);
lean_dec_ref(v___x_4962_);
v___y_4965_ = v___x_4990_;
goto v___jp_4964_;
}
}
else
{
size_t v___x_4991_; size_t v___x_4992_; lean_object* v___x_4993_; 
v___x_4991_ = ((size_t)0ULL);
v___x_4992_ = lean_usize_of_nat(v___x_4985_);
v___x_4993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4962_, v___x_4991_, v___x_4992_, v___x_4984_);
lean_dec_ref(v___x_4962_);
v___y_4965_ = v___x_4993_;
goto v___jp_4964_;
}
}
v___jp_4964_:
{
uint8_t v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v___x_4966_ = 2;
v___x_4967_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4967_, 0, v___y_4965_);
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1, v___x_4966_);
v___x_4968_ = lean_array_push(v___x_4963_, v___x_4967_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4968_);
v___x_4970_ = v___x_4959_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v___x_4968_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v_trace_4956_);
lean_ctor_set(v_reuseFailAlloc_4972_, 2, v_buildTime_4957_);
lean_ctor_set_uint8(v_reuseFailAlloc_4972_, sizeof(void*)*3, v_action_4954_);
lean_ctor_set_uint8(v_reuseFailAlloc_4972_, sizeof(void*)*3 + 1, v_wantsRebuild_4955_);
v___x_4970_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; 
v___x_4971_ = lean_box(0);
v_r_4941_ = v___x_4971_;
v___y_4942_ = v___x_4970_;
goto v___jp_4940_;
}
}
}
}
v___jp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 1, v___y_4942_);
lean_ctor_set(v___x_4931_, 0, v_r_4941_);
v___x_4944_ = v___x_4931_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_r_4941_);
lean_ctor_set(v_reuseFailAlloc_4945_, 1, v___y_4942_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4998_; 
lean_dec(v_a_4928_);
lean_dec_ref(v___y_4907_);
v___x_4996_ = lean_box(0);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 1, v___x_4934_);
lean_ctor_set(v___x_4931_, 0, v___x_4996_);
v___x_4998_ = v___x_4931_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___x_4934_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5013_; 
lean_dec_ref(v___y_4907_);
v_a_5002_ = lean_ctor_get(v___x_4927_, 0);
v_a_5003_ = lean_ctor_get(v___x_4927_, 1);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5005_ = v___x_4927_;
v_isShared_5006_ = v_isSharedCheck_5013_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_inc(v_a_5002_);
lean_dec(v___x_4927_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5013_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v_a_5003_);
v___x_5008_ = v___x_4923_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5003_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_trace_4920_);
lean_ctor_set(v_reuseFailAlloc_5012_, 2, v_buildTime_4921_);
lean_ctor_set_uint8(v_reuseFailAlloc_5012_, sizeof(void*)*3, v_action_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_5012_, sizeof(void*)*3 + 1, v_wantsRebuild_4919_);
v___x_5008_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
lean_object* v___x_5010_; 
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v___x_5008_);
v___x_5010_ = v___x_5005_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5002_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_5015_, lean_object* v___y_5016_, lean_object* v_inputHash_5017_, lean_object* v_pkg_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_){
_start:
{
uint8_t v_exe_boxed_5025_; uint64_t v_inputHash_boxed_5026_; lean_object* v_res_5027_; 
v_exe_boxed_5025_ = lean_unbox(v_exe_5015_);
v_inputHash_boxed_5026_ = lean_unbox_uint64(v_inputHash_5017_);
lean_dec_ref(v_inputHash_5017_);
v_res_5027_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5025_, v___y_5016_, v_inputHash_boxed_5026_, v_pkg_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
lean_dec_ref(v_a_5022_);
lean_dec(v_a_5021_);
lean_dec(v_a_5020_);
lean_dec(v_a_5019_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5028_, uint64_t v_hash_5029_, lean_object* v_a_5030_, lean_object* v_val_5031_, lean_object* v_file_5032_, lean_object* v___x_5033_, uint8_t v_restore_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v_a_5043_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5087_; uint8_t v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; uint8_t v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v_a_5108_; lean_object* v_val_5109_; lean_object* v_a_5110_; lean_object* v___y_5164_; lean_object* v_a_5170_; lean_object* v___y_5171_; lean_object* v___x_5173_; lean_object* v_a_5174_; 
lean_inc_ref(v_val_5031_);
lean_inc(v_a_5030_);
lean_inc_ref(v___y_5035_);
v___x_5173_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5028_, v___y_5035_, v_hash_5029_, v_a_5030_, v_val_5031_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
if (lean_obj_tag(v_a_5174_) == 1)
{
lean_object* v_a_5175_; lean_object* v_val_5176_; 
lean_dec_ref(v___y_5035_);
lean_dec_ref(v_val_5031_);
v_a_5175_ = lean_ctor_get(v___x_5173_, 1);
lean_inc(v_a_5175_);
lean_dec_ref(v___x_5173_);
v_val_5176_ = lean_ctor_get(v_a_5174_, 0);
lean_inc(v_val_5176_);
lean_dec_ref_known(v_a_5174_, 1);
v_a_5170_ = v_val_5176_;
v___y_5171_ = v_a_5175_;
goto v___jp_5169_;
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5178_; 
lean_dec(v_a_5174_);
v_a_5177_ = lean_ctor_get(v___x_5173_, 1);
lean_inc(v_a_5177_);
lean_dec_ref(v___x_5173_);
v___x_5178_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5028_, v___y_5035_, v_hash_5029_, v_val_5031_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v_a_5177_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v_a_5179_; 
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc(v_a_5179_);
if (lean_obj_tag(v_a_5179_) == 1)
{
lean_object* v_a_5180_; lean_object* v_val_5181_; 
v_a_5180_ = lean_ctor_get(v___x_5178_, 1);
lean_inc(v_a_5180_);
lean_dec_ref_known(v___x_5178_, 2);
v_val_5181_ = lean_ctor_get(v_a_5179_, 0);
lean_inc(v_val_5181_);
lean_dec_ref_known(v_a_5179_, 1);
v_a_5170_ = v_val_5181_;
v___y_5171_ = v_a_5180_;
goto v___jp_5169_;
}
else
{
lean_object* v_a_5182_; 
lean_dec(v_a_5179_);
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_file_5032_);
lean_dec(v_a_5030_);
v_a_5182_ = lean_ctor_get(v___x_5178_, 1);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5178_, 2);
v_a_5043_ = v_a_5182_;
goto v___jp_5042_;
}
}
else
{
v___y_5164_ = v___x_5178_;
goto v___jp_5163_;
}
}
v___jp_5042_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5044_ = lean_box(0);
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5044_);
lean_ctor_set(v___x_5045_, 1, v_a_5043_);
return v___x_5045_;
}
v___jp_5046_:
{
if (v_restore_5034_ == 0)
{
lean_object* v___x_5050_; 
lean_dec_ref(v___y_5047_);
lean_dec_ref(v_file_5032_);
v___x_5050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5050_, 0, v___y_5048_);
lean_ctor_set(v___x_5050_, 1, v___y_5049_);
return v___x_5050_;
}
else
{
lean_object* v_log_5051_; uint8_t v_action_5052_; uint8_t v_wantsRebuild_5053_; lean_object* v_trace_5054_; lean_object* v_buildTime_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5085_; 
lean_dec(v___y_5048_);
v_log_5051_ = lean_ctor_get(v___y_5049_, 0);
v_action_5052_ = lean_ctor_get_uint8(v___y_5049_, sizeof(void*)*3);
v_wantsRebuild_5053_ = lean_ctor_get_uint8(v___y_5049_, sizeof(void*)*3 + 1);
v_trace_5054_ = lean_ctor_get(v___y_5049_, 1);
v_buildTime_5055_ = lean_ctor_get(v___y_5049_, 2);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___y_5049_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5057_ = v___y_5049_;
v_isShared_5058_ = v_isSharedCheck_5085_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_buildTime_5055_);
lean_inc(v_trace_5054_);
lean_inc(v_log_5051_);
lean_dec(v___y_5049_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5085_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Lake_restoreArtifact(v_file_5032_, v___y_5047_, v_exe_5028_, v_log_5051_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5072_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
v_a_5061_ = lean_ctor_get(v___x_5059_, 1);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5063_ = v___x_5059_;
v_isShared_5064_ = v_isSharedCheck_5072_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_inc(v_a_5060_);
lean_dec(v___x_5059_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5072_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 0, v_a_5061_);
v___x_5066_ = v___x_5057_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5061_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_trace_5054_);
lean_ctor_set(v_reuseFailAlloc_5071_, 2, v_buildTime_5055_);
lean_ctor_set_uint8(v_reuseFailAlloc_5071_, sizeof(void*)*3, v_action_5052_);
lean_ctor_set_uint8(v_reuseFailAlloc_5071_, sizeof(void*)*3 + 1, v_wantsRebuild_5053_);
v___x_5066_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_a_5060_);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 1, v___x_5066_);
lean_ctor_set(v___x_5063_, 0, v___x_5067_);
v___x_5069_ = v___x_5063_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v___x_5066_);
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
else
{
lean_object* v_a_5073_; lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5084_; 
v_a_5073_ = lean_ctor_get(v___x_5059_, 0);
v_a_5074_ = lean_ctor_get(v___x_5059_, 1);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5076_ = v___x_5059_;
v_isShared_5077_ = v_isSharedCheck_5084_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_inc(v_a_5073_);
lean_dec(v___x_5059_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5084_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 0, v_a_5074_);
v___x_5079_ = v___x_5057_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5074_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_trace_5054_);
lean_ctor_set(v_reuseFailAlloc_5083_, 2, v_buildTime_5055_);
lean_ctor_set_uint8(v_reuseFailAlloc_5083_, sizeof(void*)*3, v_action_5052_);
lean_ctor_set_uint8(v_reuseFailAlloc_5083_, sizeof(void*)*3 + 1, v_wantsRebuild_5053_);
v___x_5079_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5081_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v___x_5079_);
v___x_5081_ = v___x_5076_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5073_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v___x_5079_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
}
}
}
v___jp_5086_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___y_5094_);
v___x_5096_ = l_Lake_BuildMetadata_ofFetch(v_hash_5029_, v___x_5095_);
v___x_5097_ = l_Lake_BuildMetadata_writeFile(v___x_5033_, v___x_5096_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v___x_5098_; 
lean_dec_ref_known(v___x_5097_, 1);
v___x_5098_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5098_, 0, v___y_5089_);
lean_ctor_set(v___x_5098_, 1, v___y_5093_);
lean_ctor_set(v___x_5098_, 2, v___y_5087_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*3, v___y_5088_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*3 + 1, v___y_5091_);
v___y_5047_ = v___y_5090_;
v___y_5048_ = v___y_5092_;
v___y_5049_ = v___x_5098_;
goto v___jp_5046_;
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5090_);
lean_dec_ref(v_file_5032_);
v_a_5099_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5097_, 1);
v___x_5100_ = lean_io_error_to_string(v_a_5099_);
v___x_5101_ = 3;
v___x_5102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5102_, 0, v___x_5100_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1, v___x_5101_);
v___x_5103_ = lean_array_get_size(v___y_5089_);
v___x_5104_ = lean_array_push(v___y_5089_, v___x_5102_);
v___x_5105_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
lean_ctor_set(v___x_5105_, 1, v___y_5093_);
lean_ctor_set(v___x_5105_, 2, v___y_5087_);
lean_ctor_set_uint8(v___x_5105_, sizeof(void*)*3, v___y_5088_);
lean_ctor_set_uint8(v___x_5105_, sizeof(void*)*3 + 1, v___y_5091_);
v___x_5106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5103_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
return v___x_5106_;
}
}
v___jp_5107_:
{
lean_object* v___x_5111_; 
v___x_5111_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5029_, v_a_5030_, v_a_5110_);
lean_dec(v_a_5030_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; uint8_t v___x_5113_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
v___x_5113_ = lean_unbox(v_a_5112_);
lean_dec(v_a_5112_);
if (v___x_5113_ == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5151_; 
v_a_5114_ = lean_ctor_get(v___x_5111_, 1);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5151_ == 0)
{
lean_object* v_unused_5152_; 
v_unused_5152_ = lean_ctor_get(v___x_5111_, 0);
lean_dec(v_unused_5152_);
v___x_5116_ = v___x_5111_;
v_isShared_5117_ = v_isSharedCheck_5151_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5111_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5151_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v_log_5118_; uint8_t v_action_5119_; uint8_t v_wantsRebuild_5120_; lean_object* v_trace_5121_; lean_object* v_buildTime_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5150_; 
v_log_5118_ = lean_ctor_get(v_a_5114_, 0);
v_action_5119_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*3);
v_wantsRebuild_5120_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*3 + 1);
v_trace_5121_ = lean_ctor_get(v_a_5114_, 1);
v_buildTime_5122_ = lean_ctor_get(v_a_5114_, 2);
v_isSharedCheck_5150_ = !lean_is_exclusive(v_a_5114_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5124_ = v_a_5114_;
v_isShared_5125_ = v_isSharedCheck_5150_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_buildTime_5122_);
lean_inc(v_trace_5121_);
lean_inc(v_log_5118_);
lean_dec(v_a_5114_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5150_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lake_removeFileIfExists(v_file_5032_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_descr_5127_; uint64_t v_hash_5128_; lean_object* v_ext_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; uint8_t v___x_5132_; 
lean_dec_ref_known(v___x_5126_, 1);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5116_);
v_descr_5127_ = lean_ctor_get(v_val_5109_, 0);
v_hash_5128_ = lean_ctor_get_uint64(v_descr_5127_, sizeof(void*)*1);
v_ext_5129_ = lean_ctor_get(v_descr_5127_, 0);
v___x_5130_ = lean_string_utf8_byte_size(v_ext_5129_);
v___x_5131_ = lean_unsigned_to_nat(0u);
v___x_5132_ = lean_nat_dec_eq(v___x_5130_, v___x_5131_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5133_ = l_Lake_lowerHexUInt64(v_hash_5128_);
v___x_5134_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5135_ = lean_string_append(v___x_5133_, v___x_5134_);
v___x_5136_ = lean_string_append(v___x_5135_, v_ext_5129_);
v___y_5087_ = v_buildTime_5122_;
v___y_5088_ = v_action_5119_;
v___y_5089_ = v_log_5118_;
v___y_5090_ = v_val_5109_;
v___y_5091_ = v_wantsRebuild_5120_;
v___y_5092_ = v_a_5108_;
v___y_5093_ = v_trace_5121_;
v___y_5094_ = v___x_5136_;
goto v___jp_5086_;
}
else
{
lean_object* v___x_5137_; 
v___x_5137_ = l_Lake_lowerHexUInt64(v_hash_5128_);
v___y_5087_ = v_buildTime_5122_;
v___y_5088_ = v_action_5119_;
v___y_5089_ = v_log_5118_;
v___y_5090_ = v_val_5109_;
v___y_5091_ = v_wantsRebuild_5120_;
v___y_5092_ = v_a_5108_;
v___y_5093_ = v_trace_5121_;
v___y_5094_ = v___x_5137_;
goto v___jp_5086_;
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5145_; 
lean_dec_ref(v_val_5109_);
lean_dec(v_a_5108_);
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_file_5032_);
v_a_5138_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5138_);
lean_dec_ref_known(v___x_5126_, 1);
v___x_5139_ = lean_io_error_to_string(v_a_5138_);
v___x_5140_ = 3;
v___x_5141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1, v___x_5140_);
v___x_5142_ = lean_array_get_size(v_log_5118_);
v___x_5143_ = lean_array_push(v_log_5118_, v___x_5141_);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v___x_5143_);
v___x_5145_ = v___x_5124_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5143_);
lean_ctor_set(v_reuseFailAlloc_5149_, 1, v_trace_5121_);
lean_ctor_set(v_reuseFailAlloc_5149_, 2, v_buildTime_5122_);
lean_ctor_set_uint8(v_reuseFailAlloc_5149_, sizeof(void*)*3, v_action_5119_);
lean_ctor_set_uint8(v_reuseFailAlloc_5149_, sizeof(void*)*3 + 1, v_wantsRebuild_5120_);
v___x_5145_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5147_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set_tag(v___x_5116_, 1);
lean_ctor_set(v___x_5116_, 1, v___x_5145_);
lean_ctor_set(v___x_5116_, 0, v___x_5142_);
v___x_5147_ = v___x_5116_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5142_);
lean_ctor_set(v_reuseFailAlloc_5148_, 1, v___x_5145_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
}
}
else
{
lean_object* v_a_5153_; 
lean_dec_ref(v___x_5033_);
v_a_5153_ = lean_ctor_get(v___x_5111_, 1);
lean_inc(v_a_5153_);
lean_dec_ref_known(v___x_5111_, 2);
v___y_5047_ = v_val_5109_;
v___y_5048_ = v_a_5108_;
v___y_5049_ = v_a_5153_;
goto v___jp_5046_;
}
}
else
{
lean_object* v_a_5154_; lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_dec_ref(v_val_5109_);
lean_dec(v_a_5108_);
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_file_5032_);
v_a_5154_ = lean_ctor_get(v___x_5111_, 0);
v_a_5155_ = lean_ctor_get(v___x_5111_, 1);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5111_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_inc(v_a_5154_);
lean_dec(v___x_5111_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5154_);
lean_ctor_set(v_reuseFailAlloc_5161_, 1, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
v___jp_5163_:
{
if (lean_obj_tag(v___y_5164_) == 0)
{
lean_object* v_a_5165_; 
v_a_5165_ = lean_ctor_get(v___y_5164_, 0);
if (lean_obj_tag(v_a_5165_) == 1)
{
lean_object* v_a_5166_; lean_object* v_val_5167_; 
lean_inc_ref(v_a_5165_);
v_a_5166_ = lean_ctor_get(v___y_5164_, 1);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___y_5164_, 2);
v_val_5167_ = lean_ctor_get(v_a_5165_, 0);
lean_inc(v_val_5167_);
v_a_5108_ = v_a_5165_;
v_val_5109_ = v_val_5167_;
v_a_5110_ = v_a_5166_;
goto v___jp_5107_;
}
else
{
lean_object* v_a_5168_; 
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_file_5032_);
lean_dec(v_a_5030_);
v_a_5168_ = lean_ctor_get(v___y_5164_, 1);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___y_5164_, 2);
v_a_5043_ = v_a_5168_;
goto v___jp_5042_;
}
}
else
{
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_file_5032_);
lean_dec(v_a_5030_);
return v___y_5164_;
}
}
v___jp_5169_:
{
lean_object* v___x_5172_; 
lean_inc_ref(v_a_5170_);
v___x_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5172_, 0, v_a_5170_);
v_a_5108_ = v___x_5172_;
v_val_5109_ = v_a_5170_;
v_a_5110_ = v___y_5171_;
goto v___jp_5107_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5183_, lean_object* v_hash_5184_, lean_object* v_a_5185_, lean_object* v_val_5186_, lean_object* v_file_5187_, lean_object* v___x_5188_, lean_object* v_restore_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
uint8_t v_exe_boxed_5197_; uint64_t v_hash_boxed_5198_; uint8_t v_restore_boxed_5199_; lean_object* v_res_5200_; 
v_exe_boxed_5197_ = lean_unbox(v_exe_5183_);
v_hash_boxed_5198_ = lean_unbox_uint64(v_hash_5184_);
lean_dec_ref(v_hash_5184_);
v_restore_boxed_5199_ = lean_unbox(v_restore_5189_);
v_res_5200_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5197_, v_hash_boxed_5198_, v_a_5185_, v_val_5186_, v_file_5187_, v___x_5188_, v_restore_boxed_5199_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec(v___y_5191_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5201_, lean_object* v_file_5202_, lean_object* v_ext_5203_, uint8_t v_text_5204_, uint8_t v_exe_5205_, uint8_t v___y_5206_, lean_object* v_val_5207_, uint64_t v_hash_5208_, uint8_t v_a_5209_, lean_object* v_____r_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
uint8_t v___x_5218_; uint8_t v___x_5219_; uint8_t v___x_5220_; 
v___x_5218_ = 1;
v___x_5219_ = l_Lake_instDecidableEqOutputStatus(v_a_5201_, v___x_5218_);
v___x_5220_ = lean_bool_not(v___x_5219_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
lean_dec_ref(v_val_5207_);
v___x_5221_ = l_Lake_computeArtifact___redArg(v_file_5202_, v_ext_5203_, v_text_5204_, v___y_5215_, v___y_5216_);
return v___x_5221_;
}
else
{
lean_object* v_toContext_5222_; lean_object* v_log_5223_; uint8_t v_action_5224_; uint8_t v_wantsRebuild_5225_; lean_object* v_trace_5226_; lean_object* v_buildTime_5227_; lean_object* v_lakeCache_5228_; lean_object* v___x_5229_; 
v_toContext_5222_ = lean_ctor_get(v___y_5215_, 1);
v_log_5223_ = lean_ctor_get(v___y_5216_, 0);
v_action_5224_ = lean_ctor_get_uint8(v___y_5216_, sizeof(void*)*3);
v_wantsRebuild_5225_ = lean_ctor_get_uint8(v___y_5216_, sizeof(void*)*3 + 1);
v_trace_5226_ = lean_ctor_get(v___y_5216_, 1);
v_buildTime_5227_ = lean_ctor_get(v___y_5216_, 2);
v_lakeCache_5228_ = lean_ctor_get(v_toContext_5222_, 2);
lean_inc_ref(v_lakeCache_5228_);
v___x_5229_ = l_Lake_Cache_saveArtifact(v_lakeCache_5228_, v_file_5202_, v_ext_5203_, v_text_5204_, v_exe_5205_, v___y_5206_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5271_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5232_ = v___x_5229_;
v_isShared_5233_ = v_isSharedCheck_5271_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5229_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5271_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v_descr_5234_; uint64_t v_hash_5235_; lean_object* v_ext_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___y_5240_; lean_object* v___x_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; 
v_descr_5234_ = lean_ctor_get(v_a_5230_, 0);
v_hash_5235_ = lean_ctor_get_uint64(v_descr_5234_, sizeof(void*)*1);
v_ext_5236_ = lean_ctor_get(v_descr_5234_, 0);
v___x_5237_ = l_Lake_Package_cacheScope(v_val_5207_);
v___x_5238_ = lean_box(0);
v___x_5263_ = lean_string_utf8_byte_size(v_ext_5236_);
v___x_5264_ = lean_unsigned_to_nat(0u);
v___x_5265_ = lean_nat_dec_eq(v___x_5263_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5266_ = l_Lake_lowerHexUInt64(v_hash_5235_);
v___x_5267_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5268_ = lean_string_append(v___x_5266_, v___x_5267_);
v___x_5269_ = lean_string_append(v___x_5268_, v_ext_5236_);
v___y_5240_ = v___x_5269_;
goto v___jp_5239_;
}
else
{
lean_object* v___x_5270_; 
v___x_5270_ = l_Lake_lowerHexUInt64(v_hash_5235_);
v___y_5240_ = v___x_5270_;
goto v___jp_5239_;
}
v___jp_5239_:
{
lean_object* v___x_5242_; 
if (v_isShared_5233_ == 0)
{
lean_ctor_set_tag(v___x_5232_, 3);
lean_ctor_set(v___x_5232_, 0, v___y_5240_);
v___x_5242_ = v___x_5232_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___y_5240_);
v___x_5242_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
lean_object* v___x_5243_; 
lean_inc_ref(v_lakeCache_5228_);
v___x_5243_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5228_, v___x_5237_, v_hash_5208_, v___x_5242_, v___x_5238_, v___x_5238_, v_a_5209_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v___x_5244_; 
lean_dec_ref_known(v___x_5243_, 1);
v___x_5244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5244_, 0, v_a_5230_);
lean_ctor_set(v___x_5244_, 1, v___y_5216_);
return v___x_5244_;
}
else
{
lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5258_; 
lean_inc(v_buildTime_5227_);
lean_inc_ref(v_trace_5226_);
lean_inc_ref(v_log_5223_);
lean_dec(v_a_5230_);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___y_5216_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; lean_object* v_unused_5260_; lean_object* v_unused_5261_; 
v_unused_5259_ = lean_ctor_get(v___y_5216_, 2);
lean_dec(v_unused_5259_);
v_unused_5260_ = lean_ctor_get(v___y_5216_, 1);
lean_dec(v_unused_5260_);
v_unused_5261_ = lean_ctor_get(v___y_5216_, 0);
lean_dec(v_unused_5261_);
v___x_5246_ = v___y_5216_;
v_isShared_5247_ = v_isSharedCheck_5258_;
goto v_resetjp_5245_;
}
else
{
lean_dec(v___y_5216_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5258_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v_a_5248_; lean_object* v___x_5249_; uint8_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5255_; 
v_a_5248_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5243_, 1);
v___x_5249_ = lean_io_error_to_string(v_a_5248_);
v___x_5250_ = 3;
v___x_5251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5251_, 0, v___x_5249_);
lean_ctor_set_uint8(v___x_5251_, sizeof(void*)*1, v___x_5250_);
v___x_5252_ = lean_array_get_size(v_log_5223_);
v___x_5253_ = lean_array_push(v_log_5223_, v___x_5251_);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5253_);
v___x_5255_ = v___x_5246_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5253_);
lean_ctor_set(v_reuseFailAlloc_5257_, 1, v_trace_5226_);
lean_ctor_set(v_reuseFailAlloc_5257_, 2, v_buildTime_5227_);
lean_ctor_set_uint8(v_reuseFailAlloc_5257_, sizeof(void*)*3, v_action_5224_);
lean_ctor_set_uint8(v_reuseFailAlloc_5257_, sizeof(void*)*3 + 1, v_wantsRebuild_5225_);
v___x_5255_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
lean_object* v___x_5256_; 
v___x_5256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5256_, 0, v___x_5252_);
lean_ctor_set(v___x_5256_, 1, v___x_5255_);
return v___x_5256_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5285_; 
lean_inc(v_buildTime_5227_);
lean_inc_ref(v_trace_5226_);
lean_inc_ref(v_log_5223_);
lean_dec_ref(v_val_5207_);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___y_5216_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; lean_object* v_unused_5287_; lean_object* v_unused_5288_; 
v_unused_5286_ = lean_ctor_get(v___y_5216_, 2);
lean_dec(v_unused_5286_);
v_unused_5287_ = lean_ctor_get(v___y_5216_, 1);
lean_dec(v_unused_5287_);
v_unused_5288_ = lean_ctor_get(v___y_5216_, 0);
lean_dec(v_unused_5288_);
v___x_5273_ = v___y_5216_;
v_isShared_5274_ = v_isSharedCheck_5285_;
goto v_resetjp_5272_;
}
else
{
lean_dec(v___y_5216_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5285_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v_a_5275_; lean_object* v___x_5276_; uint8_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5282_; 
v_a_5275_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5275_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5276_ = lean_io_error_to_string(v_a_5275_);
v___x_5277_ = 3;
v___x_5278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set_uint8(v___x_5278_, sizeof(void*)*1, v___x_5277_);
v___x_5279_ = lean_array_get_size(v_log_5223_);
v___x_5280_ = lean_array_push(v_log_5223_, v___x_5278_);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 0, v___x_5280_);
v___x_5282_ = v___x_5273_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5280_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v_trace_5226_);
lean_ctor_set(v_reuseFailAlloc_5284_, 2, v_buildTime_5227_);
lean_ctor_set_uint8(v_reuseFailAlloc_5284_, sizeof(void*)*3, v_action_5224_);
lean_ctor_set_uint8(v_reuseFailAlloc_5284_, sizeof(void*)*3 + 1, v_wantsRebuild_5225_);
v___x_5282_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
lean_object* v___x_5283_; 
v___x_5283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5279_);
lean_ctor_set(v___x_5283_, 1, v___x_5282_);
return v___x_5283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5289_ = _args[0];
lean_object* v_file_5290_ = _args[1];
lean_object* v_ext_5291_ = _args[2];
lean_object* v_text_5292_ = _args[3];
lean_object* v_exe_5293_ = _args[4];
lean_object* v___y_5294_ = _args[5];
lean_object* v_val_5295_ = _args[6];
lean_object* v_hash_5296_ = _args[7];
lean_object* v_a_5297_ = _args[8];
lean_object* v_____r_5298_ = _args[9];
lean_object* v___y_5299_ = _args[10];
lean_object* v___y_5300_ = _args[11];
lean_object* v___y_5301_ = _args[12];
lean_object* v___y_5302_ = _args[13];
lean_object* v___y_5303_ = _args[14];
lean_object* v___y_5304_ = _args[15];
lean_object* v___y_5305_ = _args[16];
_start:
{
uint8_t v_a_297063__boxed_5306_; uint8_t v_text_boxed_5307_; uint8_t v_exe_boxed_5308_; uint8_t v___y_297064__boxed_5309_; uint64_t v_hash_boxed_5310_; uint8_t v_a_297066__boxed_5311_; lean_object* v_res_5312_; 
v_a_297063__boxed_5306_ = lean_unbox(v_a_5289_);
v_text_boxed_5307_ = lean_unbox(v_text_5292_);
v_exe_boxed_5308_ = lean_unbox(v_exe_5293_);
v___y_297064__boxed_5309_ = lean_unbox(v___y_5294_);
v_hash_boxed_5310_ = lean_unbox_uint64(v_hash_5296_);
lean_dec_ref(v_hash_5296_);
v_a_297066__boxed_5311_ = lean_unbox(v_a_5297_);
v_res_5312_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_297063__boxed_5306_, v_file_5290_, v_ext_5291_, v_text_boxed_5307_, v_exe_boxed_5308_, v___y_297064__boxed_5309_, v_val_5295_, v_hash_boxed_5310_, v_a_297066__boxed_5311_, v_____r_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5313_, lean_object* v_build_5314_, uint8_t v_text_5315_, lean_object* v_ext_5316_, uint8_t v_restore_5317_, uint8_t v_exe_5318_, uint8_t v_platformIndependent_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
lean_object* v_log_5327_; uint8_t v_action_5328_; uint8_t v_wantsRebuild_5329_; lean_object* v_trace_5330_; lean_object* v_buildTime_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5596_; 
v_log_5327_ = lean_ctor_get(v_a_5325_, 0);
v_action_5328_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3);
v_wantsRebuild_5329_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3 + 1);
v_trace_5330_ = lean_ctor_get(v_a_5325_, 1);
v_buildTime_5331_ = lean_ctor_get(v_a_5325_, 2);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_a_5325_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5333_ = v_a_5325_;
v_isShared_5334_ = v_isSharedCheck_5596_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_buildTime_5331_);
lean_inc(v_trace_5330_);
lean_inc(v_log_5327_);
lean_dec(v_a_5325_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5596_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v_art_5338_; lean_object* v___y_5339_; lean_object* v___y_5355_; lean_object* v_log_5356_; uint8_t v_action_5357_; uint8_t v_wantsRebuild_5358_; lean_object* v_buildTime_5359_; lean_object* v___x_5365_; 
v___x_5335_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5313_);
v___x_5336_ = lean_string_append(v_file_5313_, v___x_5335_);
lean_inc_ref(v___x_5336_);
v___x_5365_ = l_Lake_readTraceFile(v___x_5336_, v_log_5327_);
if (lean_obj_tag(v___x_5365_) == 0)
{
if (lean_obj_tag(v_a_5321_) == 1)
{
lean_object* v_a_5366_; lean_object* v_a_5367_; lean_object* v_val_5368_; uint64_t v_hash_5369_; lean_object* v_mtime_5370_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; uint8_t v___y_5376_; uint8_t v___y_5377_; lean_object* v___y_5378_; lean_object* v___y_5379_; lean_object* v___y_5380_; lean_object* v_wsIdx_5384_; lean_object* v_config_5385_; lean_object* v_a_5387_; lean_object* v_a_5388_; lean_object* v___y_5418_; lean_object* v_enableArtifactCache_x3f_5421_; lean_object* v_restoreAllArtifacts_x3f_5422_; uint8_t v___y_5424_; lean_object* v___y_5425_; uint8_t v___y_5426_; uint8_t v___y_5466_; uint8_t v___y_5467_; uint8_t v_a_5468_; lean_object* v_a_5469_; uint8_t v___y_5471_; lean_object* v_a_5472_; uint8_t v___y_5489_; uint8_t v_a_5490_; lean_object* v_a_5491_; lean_object* v_a_5494_; uint8_t v_a_5528_; lean_object* v_a_5529_; lean_object* v___x_5545_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
v_a_5367_ = lean_ctor_get(v___x_5365_, 1);
lean_inc(v_a_5367_);
lean_dec_ref_known(v___x_5365_, 2);
v_val_5368_ = lean_ctor_get(v_a_5321_, 0);
v_hash_5369_ = lean_ctor_get_uint64(v_trace_5330_, sizeof(void*)*3);
v_mtime_5370_ = lean_ctor_get(v_trace_5330_, 2);
v_wsIdx_5384_ = lean_ctor_get(v_val_5368_, 0);
v_config_5385_ = lean_ctor_get(v_val_5368_, 6);
v_enableArtifactCache_x3f_5421_ = lean_ctor_get(v_config_5385_, 24);
v_restoreAllArtifacts_x3f_5422_ = lean_ctor_get(v_config_5385_, 25);
lean_inc_ref(v_trace_5330_);
v___x_5545_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5545_, 0, v_a_5367_);
lean_ctor_set(v___x_5545_, 1, v_trace_5330_);
lean_ctor_set(v___x_5545_, 2, v_buildTime_5331_);
lean_ctor_set_uint8(v___x_5545_, sizeof(void*)*3, v_action_5328_);
lean_ctor_set_uint8(v___x_5545_, sizeof(void*)*3 + 1, v_wantsRebuild_5329_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5421_) == 0)
{
lean_object* v_toContext_5546_; lean_object* v_lakeEnv_5547_; lean_object* v_enableArtifactCache_x3f_5548_; 
v_toContext_5546_ = lean_ctor_get(v_a_5324_, 1);
v_lakeEnv_5547_ = lean_ctor_get(v_toContext_5546_, 0);
v_enableArtifactCache_x3f_5548_ = lean_ctor_get(v_lakeEnv_5547_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5548_) == 0)
{
lean_object* v_packages_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v_config_5552_; lean_object* v_enableArtifactCache_x3f_5553_; 
v_packages_5549_ = lean_ctor_get(v_toContext_5546_, 4);
v___x_5550_ = lean_unsigned_to_nat(0u);
v___x_5551_ = lean_array_fget_borrowed(v_packages_5549_, v___x_5550_);
v_config_5552_ = lean_ctor_get(v___x_5551_, 6);
v_enableArtifactCache_x3f_5553_ = lean_ctor_get(v_config_5552_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5553_) == 0)
{
v_a_5494_ = v___x_5545_;
goto v___jp_5493_;
}
else
{
lean_object* v_val_5554_; uint8_t v___x_5555_; 
v_val_5554_ = lean_ctor_get(v_enableArtifactCache_x3f_5553_, 0);
v___x_5555_ = lean_unbox(v_val_5554_);
v_a_5528_ = v___x_5555_;
v_a_5529_ = v___x_5545_;
goto v___jp_5527_;
}
}
else
{
lean_object* v_val_5556_; uint8_t v___x_5557_; 
v_val_5556_ = lean_ctor_get(v_enableArtifactCache_x3f_5548_, 0);
v___x_5557_ = lean_unbox(v_val_5556_);
v_a_5528_ = v___x_5557_;
v_a_5529_ = v___x_5545_;
goto v___jp_5527_;
}
}
else
{
lean_object* v_val_5558_; uint8_t v___x_5559_; 
v_val_5558_ = lean_ctor_get(v_enableArtifactCache_x3f_5421_, 0);
v___x_5559_ = lean_unbox(v_val_5558_);
v_a_5528_ = v___x_5559_;
v_a_5529_ = v___x_5545_;
goto v___jp_5527_;
}
v___jp_5371_:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
lean_dec_ref(v___y_5375_);
v___x_5381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5381_, 0, v___y_5380_);
v___x_5382_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5369_, v___x_5381_, v___y_5378_, v_platformIndependent_5319_);
v___x_5383_ = lean_st_ref_set(v___y_5374_, v___x_5382_);
v___y_5355_ = v___y_5373_;
v_log_5356_ = v___y_5379_;
v_action_5357_ = v___y_5377_;
v_wantsRebuild_5358_ = v___y_5376_;
v_buildTime_5359_ = v___y_5372_;
goto v___jp_5354_;
}
v___jp_5386_:
{
lean_object* v___x_5389_; uint8_t v___x_5390_; 
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = lean_nat_dec_eq(v_wsIdx_5384_, v___x_5389_);
if (v___x_5390_ == 0)
{
lean_object* v_log_5391_; uint8_t v_action_5392_; uint8_t v_wantsRebuild_5393_; lean_object* v_buildTime_5394_; 
v_log_5391_ = lean_ctor_get(v_a_5388_, 0);
lean_inc_ref(v_log_5391_);
v_action_5392_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3);
v_wantsRebuild_5393_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3 + 1);
v_buildTime_5394_ = lean_ctor_get(v_a_5388_, 2);
lean_inc(v_buildTime_5394_);
lean_dec_ref(v_a_5388_);
v___y_5355_ = v_a_5387_;
v_log_5356_ = v_log_5391_;
v_action_5357_ = v_action_5392_;
v_wantsRebuild_5358_ = v_wantsRebuild_5393_;
v_buildTime_5359_ = v_buildTime_5394_;
goto v___jp_5354_;
}
else
{
lean_object* v_outputsRef_x3f_5395_; 
v_outputsRef_x3f_5395_ = lean_ctor_get(v_a_5324_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5395_) == 1)
{
lean_object* v_log_5396_; uint8_t v_action_5397_; uint8_t v_wantsRebuild_5398_; lean_object* v_trace_5399_; lean_object* v_buildTime_5400_; lean_object* v_val_5401_; lean_object* v___x_5402_; lean_object* v_descr_5403_; uint64_t v_hash_5404_; lean_object* v_ext_5405_; lean_object* v___x_5406_; uint8_t v___x_5407_; 
v_log_5396_ = lean_ctor_get(v_a_5388_, 0);
lean_inc_ref(v_log_5396_);
v_action_5397_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3);
v_wantsRebuild_5398_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3 + 1);
v_trace_5399_ = lean_ctor_get(v_a_5388_, 1);
lean_inc_ref(v_trace_5399_);
v_buildTime_5400_ = lean_ctor_get(v_a_5388_, 2);
lean_inc(v_buildTime_5400_);
lean_dec_ref(v_a_5388_);
v_val_5401_ = lean_ctor_get(v_outputsRef_x3f_5395_, 0);
v___x_5402_ = lean_st_ref_take(v_val_5401_);
v_descr_5403_ = lean_ctor_get(v_a_5387_, 0);
v_hash_5404_ = lean_ctor_get_uint64(v_descr_5403_, sizeof(void*)*1);
v_ext_5405_ = lean_ctor_get(v_descr_5403_, 0);
v___x_5406_ = lean_string_utf8_byte_size(v_ext_5405_);
v___x_5407_ = lean_nat_dec_eq(v___x_5406_, v___x_5389_);
if (v___x_5407_ == 0)
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5408_ = l_Lake_lowerHexUInt64(v_hash_5404_);
v___x_5409_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5410_ = lean_string_append(v___x_5408_, v___x_5409_);
v___x_5411_ = lean_string_append(v___x_5410_, v_ext_5405_);
v___y_5372_ = v_buildTime_5400_;
v___y_5373_ = v_a_5387_;
v___y_5374_ = v_val_5401_;
v___y_5375_ = v_trace_5399_;
v___y_5376_ = v_wantsRebuild_5398_;
v___y_5377_ = v_action_5397_;
v___y_5378_ = v___x_5402_;
v___y_5379_ = v_log_5396_;
v___y_5380_ = v___x_5411_;
goto v___jp_5371_;
}
else
{
lean_object* v___x_5412_; 
v___x_5412_ = l_Lake_lowerHexUInt64(v_hash_5404_);
v___y_5372_ = v_buildTime_5400_;
v___y_5373_ = v_a_5387_;
v___y_5374_ = v_val_5401_;
v___y_5375_ = v_trace_5399_;
v___y_5376_ = v_wantsRebuild_5398_;
v___y_5377_ = v_action_5397_;
v___y_5378_ = v___x_5402_;
v___y_5379_ = v_log_5396_;
v___y_5380_ = v___x_5412_;
goto v___jp_5371_;
}
}
else
{
lean_object* v_log_5413_; uint8_t v_action_5414_; uint8_t v_wantsRebuild_5415_; lean_object* v_buildTime_5416_; 
v_log_5413_ = lean_ctor_get(v_a_5388_, 0);
lean_inc_ref(v_log_5413_);
v_action_5414_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3);
v_wantsRebuild_5415_ = lean_ctor_get_uint8(v_a_5388_, sizeof(void*)*3 + 1);
v_buildTime_5416_ = lean_ctor_get(v_a_5388_, 2);
lean_inc(v_buildTime_5416_);
lean_dec_ref(v_a_5388_);
v___y_5355_ = v_a_5387_;
v_log_5356_ = v_log_5413_;
v_action_5357_ = v_action_5414_;
v_wantsRebuild_5358_ = v_wantsRebuild_5415_;
v_buildTime_5359_ = v_buildTime_5416_;
goto v___jp_5354_;
}
}
}
v___jp_5417_:
{
if (lean_obj_tag(v___y_5418_) == 0)
{
lean_object* v_a_5419_; lean_object* v_a_5420_; 
v_a_5419_ = lean_ctor_get(v___y_5418_, 0);
lean_inc(v_a_5419_);
v_a_5420_ = lean_ctor_get(v___y_5418_, 1);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___y_5418_, 2);
v_a_5387_ = v_a_5419_;
v_a_5388_ = v_a_5420_;
goto v___jp_5386_;
}
else
{
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
return v___y_5418_;
}
}
v___jp_5423_:
{
lean_object* v___x_5427_; 
lean_inc_ref(v_a_5320_);
lean_inc_ref(v___x_5336_);
lean_inc_ref(v_file_5313_);
lean_inc(v_val_5368_);
lean_inc(v_a_5366_);
v___x_5427_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5318_, v_hash_5369_, v_a_5366_, v_val_5368_, v_file_5313_, v___x_5336_, v___y_5426_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v___y_5425_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_a_5428_; 
v_a_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_a_5428_);
if (lean_obj_tag(v_a_5428_) == 1)
{
lean_object* v_a_5429_; lean_object* v_val_5430_; 
lean_dec(v_a_5366_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5429_ = lean_ctor_get(v___x_5427_, 1);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5427_, 2);
v_val_5430_ = lean_ctor_get(v_a_5428_, 0);
lean_inc(v_val_5430_);
lean_dec_ref_known(v_a_5428_, 1);
v_a_5387_ = v_val_5430_;
v_a_5388_ = v_a_5429_;
goto v___jp_5386_;
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5432_; 
lean_dec(v_a_5428_);
v_a_5431_ = lean_ctor_get(v___x_5427_, 1);
lean_inc(v_a_5431_);
lean_dec_ref_known(v___x_5427_, 2);
v___x_5432_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5320_, v_file_5313_, v_trace_5330_, v_a_5366_, v_mtime_5370_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5431_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v_a_5434_; uint8_t v___x_5435_; uint8_t v___x_5436_; uint8_t v___x_5437_; uint8_t v___x_5438_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
lean_inc(v_a_5433_);
v_a_5434_ = lean_ctor_get(v___x_5432_, 1);
lean_inc(v_a_5434_);
lean_dec_ref_known(v___x_5432_, 2);
v___x_5435_ = 0;
v___x_5436_ = lean_unbox(v_a_5433_);
v___x_5437_ = l_Lake_instDecidableEqOutputStatus(v___x_5436_, v___x_5435_);
v___x_5438_ = lean_bool_not(v___x_5437_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
lean_inc_ref(v_a_5320_);
lean_inc_ref(v___x_5336_);
lean_inc_ref(v_ext_5316_);
lean_inc_ref(v_file_5313_);
v___x_5439_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5313_, v_build_5314_, v_text_5315_, v_ext_5316_, v_trace_5330_, v___x_5336_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5434_);
lean_dec_ref(v_trace_5330_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5441_; uint8_t v___x_5442_; lean_object* v___x_5443_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 1);
lean_inc(v_a_5440_);
lean_dec_ref_known(v___x_5439_, 2);
v___x_5441_ = lean_box(0);
v___x_5442_ = lean_unbox(v_a_5433_);
lean_dec(v_a_5433_);
lean_inc(v_val_5368_);
v___x_5443_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5442_, v_file_5313_, v_ext_5316_, v_text_5315_, v_exe_5318_, v___y_5426_, v_val_5368_, v_hash_5369_, v___y_5424_, v___x_5441_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5440_);
lean_dec_ref(v_a_5320_);
v___y_5418_ = v___x_5443_;
goto v___jp_5417_;
}
else
{
lean_dec(v_a_5433_);
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_file_5313_);
return v___x_5439_;
}
}
else
{
lean_object* v___x_5444_; uint8_t v___x_5445_; lean_object* v___x_5446_; 
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_build_5314_);
v___x_5444_ = lean_box(0);
v___x_5445_ = lean_unbox(v_a_5433_);
lean_dec(v_a_5433_);
lean_inc(v_val_5368_);
v___x_5446_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5445_, v_file_5313_, v_ext_5316_, v_text_5315_, v_exe_5318_, v___y_5426_, v_val_5368_, v_hash_5369_, v___y_5424_, v___x_5444_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5434_);
lean_dec_ref(v_a_5320_);
v___y_5418_ = v___x_5446_;
goto v___jp_5417_;
}
}
else
{
lean_object* v_a_5447_; lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5447_ = lean_ctor_get(v___x_5432_, 0);
v_a_5448_ = lean_ctor_get(v___x_5432_, 1);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___x_5432_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_inc(v_a_5447_);
lean_dec(v___x_5432_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5447_);
lean_ctor_set(v_reuseFailAlloc_5454_, 1, v_a_5448_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
}
else
{
lean_object* v_a_5456_; lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5464_; 
lean_dec(v_a_5366_);
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5456_ = lean_ctor_get(v___x_5427_, 0);
v_a_5457_ = lean_ctor_get(v___x_5427_, 1);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___x_5427_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5459_ = v___x_5427_;
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_inc(v_a_5456_);
lean_dec(v___x_5427_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5462_; 
if (v_isShared_5460_ == 0)
{
v___x_5462_ = v___x_5459_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5456_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_a_5457_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
}
}
v___jp_5465_:
{
if (v_restore_5317_ == 0)
{
v___y_5424_ = v___y_5466_;
v___y_5425_ = v_a_5469_;
v___y_5426_ = v_a_5468_;
goto v___jp_5423_;
}
else
{
v___y_5424_ = v___y_5466_;
v___y_5425_ = v_a_5469_;
v___y_5426_ = v___y_5467_;
goto v___jp_5423_;
}
}
v___jp_5470_:
{
lean_object* v___x_5473_; 
lean_inc_ref(v_a_5320_);
lean_inc_ref(v___x_5336_);
lean_inc_ref(v_file_5313_);
lean_inc(v_val_5368_);
v___x_5473_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5318_, v_hash_5369_, v_a_5366_, v_val_5368_, v_file_5313_, v___x_5336_, v___y_5471_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5472_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
if (lean_obj_tag(v_a_5474_) == 1)
{
lean_object* v_a_5475_; lean_object* v_val_5476_; 
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5475_ = lean_ctor_get(v___x_5473_, 1);
lean_inc(v_a_5475_);
lean_dec_ref_known(v___x_5473_, 2);
v_val_5476_ = lean_ctor_get(v_a_5474_, 0);
lean_inc(v_val_5476_);
lean_dec_ref_known(v_a_5474_, 1);
v_a_5387_ = v_val_5476_;
v_a_5388_ = v_a_5475_;
goto v___jp_5386_;
}
else
{
lean_object* v_a_5477_; lean_object* v___x_5478_; 
lean_dec(v_a_5474_);
v_a_5477_ = lean_ctor_get(v___x_5473_, 1);
lean_inc(v_a_5477_);
lean_dec_ref_known(v___x_5473_, 2);
lean_inc_ref(v___x_5336_);
v___x_5478_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5313_, v_build_5314_, v_text_5315_, v_ext_5316_, v_trace_5330_, v___x_5336_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5477_);
lean_dec_ref(v_trace_5330_);
v___y_5418_ = v___x_5478_;
goto v___jp_5417_;
}
}
else
{
lean_object* v_a_5479_; lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5487_; 
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5479_ = lean_ctor_get(v___x_5473_, 0);
v_a_5480_ = lean_ctor_get(v___x_5473_, 1);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5482_ = v___x_5473_;
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_inc(v_a_5479_);
lean_dec(v___x_5473_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5485_; 
if (v_isShared_5483_ == 0)
{
v___x_5485_ = v___x_5482_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5479_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v_a_5480_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
}
v___jp_5488_:
{
if (v_a_5490_ == 0)
{
lean_object* v___x_5492_; 
lean_dec(v_a_5366_);
lean_inc_ref(v___x_5336_);
v___x_5492_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5313_, v_build_5314_, v_text_5315_, v_ext_5316_, v_trace_5330_, v___x_5336_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5491_);
lean_dec_ref(v_trace_5330_);
v___y_5418_ = v___x_5492_;
goto v___jp_5417_;
}
else
{
v___y_5471_ = v___y_5489_;
v_a_5472_ = v_a_5491_;
goto v___jp_5470_;
}
}
v___jp_5493_:
{
lean_object* v___x_5495_; 
lean_inc(v_a_5366_);
v___x_5495_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5320_, v_file_5313_, v_trace_5330_, v_a_5366_, v_mtime_5370_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5494_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v_a_5497_; uint8_t v___x_5498_; uint8_t v___x_5499_; uint8_t v___x_5500_; uint8_t v___x_5501_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
v_a_5497_ = lean_ctor_get(v___x_5495_, 1);
lean_inc(v_a_5497_);
lean_dec_ref_known(v___x_5495_, 2);
v___x_5498_ = 0;
v___x_5499_ = lean_unbox(v_a_5496_);
lean_dec(v_a_5496_);
v___x_5500_ = l_Lake_instDecidableEqOutputStatus(v___x_5499_, v___x_5498_);
v___x_5501_ = lean_bool_not(v___x_5500_);
if (v___x_5501_ == 0)
{
uint8_t v___x_5502_; 
v___x_5502_ = 1;
if (lean_obj_tag(v_enableArtifactCache_x3f_5421_) == 0)
{
lean_object* v_toContext_5503_; lean_object* v_lakeEnv_5504_; lean_object* v_enableArtifactCache_x3f_5505_; 
v_toContext_5503_ = lean_ctor_get(v_a_5324_, 1);
v_lakeEnv_5504_ = lean_ctor_get(v_toContext_5503_, 0);
v_enableArtifactCache_x3f_5505_ = lean_ctor_get(v_lakeEnv_5504_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5505_) == 0)
{
lean_object* v_packages_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v_config_5509_; lean_object* v_enableArtifactCache_x3f_5510_; 
v_packages_5506_ = lean_ctor_get(v_toContext_5503_, 4);
v___x_5507_ = lean_unsigned_to_nat(0u);
v___x_5508_ = lean_array_fget_borrowed(v_packages_5506_, v___x_5507_);
v_config_5509_ = lean_ctor_get(v___x_5508_, 6);
v_enableArtifactCache_x3f_5510_ = lean_ctor_get(v_config_5509_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5510_) == 0)
{
v___y_5471_ = v___x_5502_;
v_a_5472_ = v_a_5497_;
goto v___jp_5470_;
}
else
{
lean_object* v_val_5511_; uint8_t v___x_5512_; 
v_val_5511_ = lean_ctor_get(v_enableArtifactCache_x3f_5510_, 0);
v___x_5512_ = lean_unbox(v_val_5511_);
v___y_5489_ = v___x_5502_;
v_a_5490_ = v___x_5512_;
v_a_5491_ = v_a_5497_;
goto v___jp_5488_;
}
}
else
{
lean_object* v_val_5513_; uint8_t v___x_5514_; 
v_val_5513_ = lean_ctor_get(v_enableArtifactCache_x3f_5505_, 0);
v___x_5514_ = lean_unbox(v_val_5513_);
v___y_5489_ = v___x_5502_;
v_a_5490_ = v___x_5514_;
v_a_5491_ = v_a_5497_;
goto v___jp_5488_;
}
}
else
{
lean_object* v_val_5515_; uint8_t v___x_5516_; 
v_val_5515_ = lean_ctor_get(v_enableArtifactCache_x3f_5421_, 0);
v___x_5516_ = lean_unbox(v_val_5515_);
v___y_5489_ = v___x_5502_;
v_a_5490_ = v___x_5516_;
v_a_5491_ = v_a_5497_;
goto v___jp_5488_;
}
}
else
{
lean_object* v___x_5517_; 
lean_dec(v_a_5366_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_build_5314_);
v___x_5517_ = l_Lake_computeArtifact___redArg(v_file_5313_, v_ext_5316_, v_text_5315_, v_a_5324_, v_a_5497_);
v___y_5418_ = v___x_5517_;
goto v___jp_5417_;
}
}
else
{
lean_object* v_a_5518_; lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v_a_5366_);
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5518_ = lean_ctor_get(v___x_5495_, 0);
v_a_5519_ = lean_ctor_get(v___x_5495_, 1);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5495_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_inc(v_a_5518_);
lean_dec(v___x_5495_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5518_);
lean_ctor_set(v_reuseFailAlloc_5525_, 1, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
v___jp_5527_:
{
if (v_a_5528_ == 0)
{
v_a_5494_ = v_a_5529_;
goto v___jp_5493_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5422_) == 0)
{
lean_object* v_toContext_5530_; lean_object* v_lakeEnv_5531_; lean_object* v_restoreAllArtifacts_x3f_5532_; 
v_toContext_5530_ = lean_ctor_get(v_a_5324_, 1);
v_lakeEnv_5531_ = lean_ctor_get(v_toContext_5530_, 0);
v_restoreAllArtifacts_x3f_5532_ = lean_ctor_get(v_lakeEnv_5531_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5532_) == 0)
{
lean_object* v_packages_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v_config_5536_; lean_object* v_restoreAllArtifacts_x3f_5537_; 
v_packages_5533_ = lean_ctor_get(v_toContext_5530_, 4);
v___x_5534_ = lean_unsigned_to_nat(0u);
v___x_5535_ = lean_array_fget_borrowed(v_packages_5533_, v___x_5534_);
v_config_5536_ = lean_ctor_get(v___x_5535_, 6);
v_restoreAllArtifacts_x3f_5537_ = lean_ctor_get(v_config_5536_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5537_) == 0)
{
uint8_t v___x_5538_; 
v___x_5538_ = 0;
v___y_5466_ = v_a_5528_;
v___y_5467_ = v_a_5528_;
v_a_5468_ = v___x_5538_;
v_a_5469_ = v_a_5529_;
goto v___jp_5465_;
}
else
{
lean_object* v_val_5539_; uint8_t v___x_5540_; 
v_val_5539_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5537_, 0);
v___x_5540_ = lean_unbox(v_val_5539_);
v___y_5466_ = v_a_5528_;
v___y_5467_ = v_a_5528_;
v_a_5468_ = v___x_5540_;
v_a_5469_ = v_a_5529_;
goto v___jp_5465_;
}
}
else
{
lean_object* v_val_5541_; uint8_t v___x_5542_; 
v_val_5541_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5532_, 0);
v___x_5542_ = lean_unbox(v_val_5541_);
v___y_5466_ = v_a_5528_;
v___y_5467_ = v_a_5528_;
v_a_5468_ = v___x_5542_;
v_a_5469_ = v_a_5529_;
goto v___jp_5465_;
}
}
else
{
lean_object* v_val_5543_; uint8_t v___x_5544_; 
v_val_5543_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5422_, 0);
v___x_5544_ = lean_unbox(v_val_5543_);
v___y_5466_ = v_a_5528_;
v___y_5467_ = v_a_5528_;
v_a_5468_ = v___x_5544_;
v_a_5469_ = v_a_5529_;
goto v___jp_5465_;
}
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v_a_5561_; lean_object* v_mtime_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
lean_del_object(v___x_5333_);
v_a_5560_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5560_);
v_a_5561_ = lean_ctor_get(v___x_5365_, 1);
lean_inc(v_a_5561_);
lean_dec_ref_known(v___x_5365_, 2);
v_mtime_5562_ = lean_ctor_get(v_trace_5330_, 2);
lean_inc_ref(v_trace_5330_);
v___x_5563_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5563_, 0, v_a_5561_);
lean_ctor_set(v___x_5563_, 1, v_trace_5330_);
lean_ctor_set(v___x_5563_, 2, v_buildTime_5331_);
lean_ctor_set_uint8(v___x_5563_, sizeof(void*)*3, v_action_5328_);
lean_ctor_set_uint8(v___x_5563_, sizeof(void*)*3 + 1, v_wantsRebuild_5329_);
v___x_5564_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5320_, v_file_5313_, v_trace_5330_, v_a_5560_, v_mtime_5562_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v___x_5563_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v_a_5566_; uint8_t v___x_5567_; uint8_t v___x_5568_; uint8_t v___x_5569_; uint8_t v___x_5570_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_a_5565_);
v_a_5566_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_a_5566_);
lean_dec_ref_known(v___x_5564_, 2);
v___x_5567_ = 0;
v___x_5568_ = lean_unbox(v_a_5565_);
lean_dec(v_a_5565_);
v___x_5569_ = l_Lake_instDecidableEqOutputStatus(v___x_5568_, v___x_5567_);
v___x_5570_ = lean_bool_not(v___x_5569_);
if (v___x_5570_ == 0)
{
lean_object* v___x_5571_; 
lean_inc_ref(v___x_5336_);
v___x_5571_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5313_, v_build_5314_, v_text_5315_, v_ext_5316_, v_trace_5330_, v___x_5336_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5566_);
lean_dec_ref(v_trace_5330_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; lean_object* v_a_5573_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_a_5572_);
v_a_5573_ = lean_ctor_get(v___x_5571_, 1);
lean_inc(v_a_5573_);
lean_dec_ref_known(v___x_5571_, 2);
v_art_5338_ = v_a_5572_;
v___y_5339_ = v_a_5573_;
goto v___jp_5337_;
}
else
{
lean_dec_ref(v___x_5336_);
return v___x_5571_;
}
}
else
{
lean_object* v___x_5574_; 
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_build_5314_);
v___x_5574_ = l_Lake_computeArtifact___redArg(v_file_5313_, v_ext_5316_, v_text_5315_, v_a_5324_, v_a_5566_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v_a_5576_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
lean_inc(v_a_5575_);
v_a_5576_ = lean_ctor_get(v___x_5574_, 1);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5574_, 2);
v_art_5338_ = v_a_5575_;
v___y_5339_ = v_a_5576_;
goto v___jp_5337_;
}
else
{
lean_dec_ref(v___x_5336_);
return v___x_5574_;
}
}
}
else
{
lean_object* v_a_5577_; lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
lean_dec_ref(v___x_5336_);
lean_dec_ref(v_trace_5330_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5577_ = lean_ctor_get(v___x_5564_, 0);
v_a_5578_ = lean_ctor_get(v___x_5564_, 1);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5564_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_inc(v_a_5577_);
lean_dec(v___x_5564_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5577_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5595_; 
lean_dec_ref(v___x_5336_);
lean_del_object(v___x_5333_);
lean_dec_ref(v_a_5320_);
lean_dec_ref(v_ext_5316_);
lean_dec_ref(v_build_5314_);
lean_dec_ref(v_file_5313_);
v_a_5586_ = lean_ctor_get(v___x_5365_, 0);
v_a_5587_ = lean_ctor_get(v___x_5365_, 1);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5589_ = v___x_5365_;
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_inc(v_a_5586_);
lean_dec(v___x_5365_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5591_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5591_, 0, v_a_5587_);
lean_ctor_set(v___x_5591_, 1, v_trace_5330_);
lean_ctor_set(v___x_5591_, 2, v_buildTime_5331_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*3, v_action_5328_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*3 + 1, v_wantsRebuild_5329_);
if (v_isShared_5590_ == 0)
{
lean_ctor_set(v___x_5589_, 1, v___x_5591_);
v___x_5593_ = v___x_5589_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5586_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
v___jp_5337_:
{
lean_object* v_log_5340_; uint8_t v_action_5341_; uint8_t v_wantsRebuild_5342_; lean_object* v_buildTime_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5352_; 
v_log_5340_ = lean_ctor_get(v___y_5339_, 0);
v_action_5341_ = lean_ctor_get_uint8(v___y_5339_, sizeof(void*)*3);
v_wantsRebuild_5342_ = lean_ctor_get_uint8(v___y_5339_, sizeof(void*)*3 + 1);
v_buildTime_5343_ = lean_ctor_get(v___y_5339_, 2);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___y_5339_);
if (v_isSharedCheck_5352_ == 0)
{
lean_object* v_unused_5353_; 
v_unused_5353_ = lean_ctor_get(v___y_5339_, 1);
lean_dec(v_unused_5353_);
v___x_5345_ = v___y_5339_;
v_isShared_5346_ = v_isSharedCheck_5352_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_buildTime_5343_);
lean_inc(v_log_5340_);
lean_dec(v___y_5339_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5352_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = l_Lake_Artifact_trace(v_art_5338_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5347_);
v___x_5349_ = v___x_5345_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_log_5340_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v___x_5347_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_buildTime_5343_);
lean_ctor_set_uint8(v_reuseFailAlloc_5351_, sizeof(void*)*3, v_action_5341_);
lean_ctor_set_uint8(v_reuseFailAlloc_5351_, sizeof(void*)*3 + 1, v_wantsRebuild_5342_);
v___x_5349_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5350_; 
v___x_5350_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5338_, v___x_5336_, v___x_5349_);
lean_dec_ref(v___x_5336_);
return v___x_5350_;
}
}
}
v___jp_5354_:
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
v___x_5360_ = l_Lake_Artifact_trace(v___y_5355_);
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 2, v_buildTime_5359_);
lean_ctor_set(v___x_5333_, 1, v___x_5360_);
lean_ctor_set(v___x_5333_, 0, v_log_5356_);
v___x_5362_ = v___x_5333_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_log_5356_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5364_, 2, v_buildTime_5359_);
v___x_5362_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5363_; 
lean_ctor_set_uint8(v___x_5362_, sizeof(void*)*3, v_action_5357_);
lean_ctor_set_uint8(v___x_5362_, sizeof(void*)*3 + 1, v_wantsRebuild_5358_);
v___x_5363_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5355_, v___x_5336_, v___x_5362_);
lean_dec_ref(v___x_5336_);
return v___x_5363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5597_, lean_object* v_build_5598_, lean_object* v_text_5599_, lean_object* v_ext_5600_, lean_object* v_restore_5601_, lean_object* v_exe_5602_, lean_object* v_platformIndependent_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_){
_start:
{
uint8_t v_text_boxed_5611_; uint8_t v_restore_boxed_5612_; uint8_t v_exe_boxed_5613_; uint8_t v_platformIndependent_boxed_5614_; lean_object* v_res_5615_; 
v_text_boxed_5611_ = lean_unbox(v_text_5599_);
v_restore_boxed_5612_ = lean_unbox(v_restore_5601_);
v_exe_boxed_5613_ = lean_unbox(v_exe_5602_);
v_platformIndependent_boxed_5614_ = lean_unbox(v_platformIndependent_5603_);
v_res_5615_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5597_, v_build_5598_, v_text_boxed_5611_, v_ext_5600_, v_restore_boxed_5612_, v_exe_boxed_5613_, v_platformIndependent_boxed_5614_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
lean_dec_ref(v_a_5608_);
lean_dec(v_a_5607_);
lean_dec(v_a_5606_);
lean_dec(v_a_5605_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5617_, lean_object* v_build_5618_, lean_object* v_file_5619_, uint8_t v_text_5620_, lean_object* v_depInfo_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v___x_5629_; 
lean_inc_ref(v___y_5626_);
lean_inc(v___y_5625_);
lean_inc(v___y_5624_);
lean_inc(v___y_5623_);
lean_inc_ref(v___y_5622_);
v___x_5629_ = lean_apply_7(v_extraDepTrace_5617_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, lean_box(0));
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_object* v_a_5630_; lean_object* v_a_5631_; lean_object* v_log_5632_; uint8_t v_action_5633_; uint8_t v_wantsRebuild_5634_; lean_object* v_trace_5635_; lean_object* v_buildTime_5636_; lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5667_; 
v_a_5630_ = lean_ctor_get(v___x_5629_, 1);
lean_inc(v_a_5630_);
v_a_5631_ = lean_ctor_get(v___x_5629_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5629_, 2);
v_log_5632_ = lean_ctor_get(v_a_5630_, 0);
v_action_5633_ = lean_ctor_get_uint8(v_a_5630_, sizeof(void*)*3);
v_wantsRebuild_5634_ = lean_ctor_get_uint8(v_a_5630_, sizeof(void*)*3 + 1);
v_trace_5635_ = lean_ctor_get(v_a_5630_, 1);
v_buildTime_5636_ = lean_ctor_get(v_a_5630_, 2);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_a_5630_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5638_ = v_a_5630_;
v_isShared_5639_ = v_isSharedCheck_5667_;
goto v_resetjp_5637_;
}
else
{
lean_inc(v_buildTime_5636_);
lean_inc(v_trace_5635_);
lean_inc(v_log_5632_);
lean_dec(v_a_5630_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5667_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
lean_object* v___x_5640_; lean_object* v___x_5642_; 
v___x_5640_ = l_Lake_BuildTrace_mix(v_trace_5635_, v_a_5631_);
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 1, v___x_5640_);
v___x_5642_ = v___x_5638_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_log_5632_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v___x_5640_);
lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_buildTime_5636_);
lean_ctor_set_uint8(v_reuseFailAlloc_5666_, sizeof(void*)*3, v_action_5633_);
lean_ctor_set_uint8(v_reuseFailAlloc_5666_, sizeof(void*)*3 + 1, v_wantsRebuild_5634_);
v___x_5642_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; uint8_t v___x_5645_; lean_object* v___x_5646_; 
v___x_5643_ = lean_apply_1(v_build_5618_, v_depInfo_5621_);
v___x_5644_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5645_ = 0;
v___x_5646_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5619_, v___x_5643_, v_text_5620_, v___x_5644_, v___x_5645_, v___x_5645_, v___x_5645_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___x_5642_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v_a_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5656_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
v_a_5648_ = lean_ctor_get(v___x_5646_, 1);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5650_ = v___x_5646_;
v_isShared_5651_ = v_isSharedCheck_5656_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_a_5648_);
lean_inc(v_a_5647_);
lean_dec(v___x_5646_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5656_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v_path_5652_; lean_object* v___x_5654_; 
v_path_5652_ = lean_ctor_get(v_a_5647_, 1);
lean_inc_ref(v_path_5652_);
lean_dec(v_a_5647_);
if (v_isShared_5651_ == 0)
{
lean_ctor_set(v___x_5650_, 0, v_path_5652_);
v___x_5654_ = v___x_5650_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_path_5652_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_a_5648_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
else
{
lean_object* v_a_5657_; lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
v_a_5657_ = lean_ctor_get(v___x_5646_, 0);
v_a_5658_ = lean_ctor_get(v___x_5646_, 1);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5646_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_inc(v_a_5657_);
lean_dec(v___x_5646_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5657_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
}
else
{
lean_object* v_a_5668_; lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_dec_ref(v___y_5622_);
lean_dec(v_depInfo_5621_);
lean_dec_ref(v_file_5619_);
lean_dec_ref(v_build_5618_);
v_a_5668_ = lean_ctor_get(v___x_5629_, 0);
v_a_5669_ = lean_ctor_get(v___x_5629_, 1);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5629_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_inc(v_a_5668_);
lean_dec(v___x_5629_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5668_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v_a_5669_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5677_, lean_object* v_build_5678_, lean_object* v_file_5679_, lean_object* v_text_5680_, lean_object* v_depInfo_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_){
_start:
{
uint8_t v_text_boxed_5689_; lean_object* v_res_5690_; 
v_text_boxed_5689_ = lean_unbox(v_text_5680_);
v_res_5690_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5677_, v_build_5678_, v_file_5679_, v_text_boxed_5689_, v_depInfo_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec(v___y_5684_);
lean_dec(v___y_5683_);
return v_res_5690_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5691_, lean_object* v_dep_5692_, lean_object* v_build_5693_, lean_object* v_extraDepTrace_5694_, uint8_t v_text_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_){
_start:
{
lean_object* v___x_5703_; lean_object* v___f_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; uint8_t v___x_5707_; lean_object* v___x_5708_; 
v___x_5703_ = lean_box(v_text_5695_);
v___f_5704_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5704_, 0, v_extraDepTrace_5694_);
lean_closure_set(v___f_5704_, 1, v_build_5693_);
lean_closure_set(v___f_5704_, 2, v_file_5691_);
lean_closure_set(v___f_5704_, 3, v___x_5703_);
v___x_5705_ = l_Lake_instDataKindFilePath;
v___x_5706_ = lean_unsigned_to_nat(0u);
v___x_5707_ = 0;
v___x_5708_ = l_Lake_Job_mapM___redArg(v___x_5705_, v_dep_5692_, v___f_5704_, v___x_5706_, v___x_5707_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_);
return v___x_5708_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5709_, lean_object* v_dep_5710_, lean_object* v_build_5711_, lean_object* v_extraDepTrace_5712_, lean_object* v_text_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_){
_start:
{
uint8_t v_text_boxed_5721_; lean_object* v_res_5722_; 
v_text_boxed_5721_ = lean_unbox(v_text_5713_);
v_res_5722_ = l_Lake_buildFileAfterDep___redArg(v_file_5709_, v_dep_5710_, v_build_5711_, v_extraDepTrace_5712_, v_text_boxed_5721_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_);
lean_dec_ref(v_a_5719_);
lean_dec_ref(v_a_5718_);
lean_dec(v_a_5717_);
lean_dec(v_a_5716_);
lean_dec(v_a_5715_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5723_, lean_object* v_file_5724_, lean_object* v_dep_5725_, lean_object* v_build_5726_, lean_object* v_extraDepTrace_5727_, uint8_t v_text_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_){
_start:
{
lean_object* v___x_5736_; lean_object* v___f_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; uint8_t v___x_5740_; lean_object* v___x_5741_; 
v___x_5736_ = lean_box(v_text_5728_);
v___f_5737_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5737_, 0, v_extraDepTrace_5727_);
lean_closure_set(v___f_5737_, 1, v_build_5726_);
lean_closure_set(v___f_5737_, 2, v_file_5724_);
lean_closure_set(v___f_5737_, 3, v___x_5736_);
v___x_5738_ = l_Lake_instDataKindFilePath;
v___x_5739_ = lean_unsigned_to_nat(0u);
v___x_5740_ = 0;
v___x_5741_ = l_Lake_Job_mapM___redArg(v___x_5738_, v_dep_5725_, v___f_5737_, v___x_5739_, v___x_5740_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_);
return v___x_5741_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5742_, lean_object* v_file_5743_, lean_object* v_dep_5744_, lean_object* v_build_5745_, lean_object* v_extraDepTrace_5746_, lean_object* v_text_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_){
_start:
{
uint8_t v_text_boxed_5755_; lean_object* v_res_5756_; 
v_text_boxed_5755_ = lean_unbox(v_text_5747_);
v_res_5756_ = l_Lake_buildFileAfterDep(v_00_u03b1_5742_, v_file_5743_, v_dep_5744_, v_build_5745_, v_extraDepTrace_5746_, v_text_boxed_5755_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_);
lean_dec_ref(v_a_5753_);
lean_dec_ref(v_a_5752_);
lean_dec(v_a_5751_);
lean_dec(v_a_5750_);
lean_dec(v_a_5749_);
return v_res_5756_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5757_){
_start:
{
lean_object* v___x_5759_; 
v___x_5759_ = l_Lake_computeBinFileHash(v_info_5757_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v___x_5761_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_a_5760_);
lean_dec_ref_known(v___x_5759_, 1);
v___x_5761_ = lean_io_metadata(v_info_5757_);
if (lean_obj_tag(v___x_5761_) == 0)
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5773_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5764_ = v___x_5761_;
v_isShared_5765_ = v_isSharedCheck_5773_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5761_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5773_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v_modified_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; uint64_t v___x_5769_; lean_object* v___x_5771_; 
v_modified_5766_ = lean_ctor_get(v_a_5762_, 1);
lean_inc_ref(v_modified_5766_);
lean_dec(v_a_5762_);
v___x_5767_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5768_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5768_, 0, v_info_5757_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
lean_ctor_set(v___x_5768_, 2, v_modified_5766_);
v___x_5769_ = lean_unbox_uint64(v_a_5760_);
lean_dec(v_a_5760_);
lean_ctor_set_uint64(v___x_5768_, sizeof(void*)*3, v___x_5769_);
if (v_isShared_5765_ == 0)
{
lean_ctor_set(v___x_5764_, 0, v___x_5768_);
v___x_5771_ = v___x_5764_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v___x_5768_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
else
{
lean_object* v_a_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5781_; 
lean_dec(v_a_5760_);
lean_dec_ref(v_info_5757_);
v_a_5774_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5776_ = v___x_5761_;
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_a_5774_);
lean_dec(v___x_5761_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5779_; 
if (v_isShared_5777_ == 0)
{
v___x_5779_ = v___x_5776_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5774_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
return v___x_5779_;
}
}
}
}
else
{
lean_object* v_a_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5789_; 
lean_dec_ref(v_info_5757_);
v_a_5782_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5784_ = v___x_5759_;
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_a_5782_);
lean_dec(v___x_5759_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5787_; 
if (v_isShared_5785_ == 0)
{
v___x_5787_ = v___x_5784_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5782_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v_res_5792_; 
v_res_5792_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5790_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_){
_start:
{
lean_object* v_log_5801_; uint8_t v_action_5802_; uint8_t v_wantsRebuild_5803_; lean_object* v_trace_5804_; lean_object* v_buildTime_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5825_; 
v_log_5801_ = lean_ctor_get(v___y_5799_, 0);
v_action_5802_ = lean_ctor_get_uint8(v___y_5799_, sizeof(void*)*3);
v_wantsRebuild_5803_ = lean_ctor_get_uint8(v___y_5799_, sizeof(void*)*3 + 1);
v_trace_5804_ = lean_ctor_get(v___y_5799_, 1);
v_buildTime_5805_ = lean_ctor_get(v___y_5799_, 2);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___y_5799_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5807_ = v___y_5799_;
v_isShared_5808_ = v_isSharedCheck_5825_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_buildTime_5805_);
lean_inc(v_trace_5804_);
lean_inc(v_log_5801_);
lean_dec(v___y_5799_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5825_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5809_; 
lean_inc_ref(v_path_5793_);
v___x_5809_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5793_);
if (lean_obj_tag(v___x_5809_) == 0)
{
lean_object* v_a_5810_; lean_object* v___x_5812_; 
lean_dec_ref(v_trace_5804_);
v_a_5810_ = lean_ctor_get(v___x_5809_, 0);
lean_inc(v_a_5810_);
lean_dec_ref_known(v___x_5809_, 1);
if (v_isShared_5808_ == 0)
{
lean_ctor_set(v___x_5807_, 1, v_a_5810_);
v___x_5812_ = v___x_5807_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_log_5801_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v_a_5810_);
lean_ctor_set(v_reuseFailAlloc_5814_, 2, v_buildTime_5805_);
lean_ctor_set_uint8(v_reuseFailAlloc_5814_, sizeof(void*)*3, v_action_5802_);
lean_ctor_set_uint8(v_reuseFailAlloc_5814_, sizeof(void*)*3 + 1, v_wantsRebuild_5803_);
v___x_5812_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
lean_object* v___x_5813_; 
v___x_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5813_, 0, v_path_5793_);
lean_ctor_set(v___x_5813_, 1, v___x_5812_);
return v___x_5813_;
}
}
else
{
lean_object* v_a_5815_; lean_object* v___x_5816_; uint8_t v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5822_; 
lean_dec_ref(v_path_5793_);
v_a_5815_ = lean_ctor_get(v___x_5809_, 0);
lean_inc(v_a_5815_);
lean_dec_ref_known(v___x_5809_, 1);
v___x_5816_ = lean_io_error_to_string(v_a_5815_);
v___x_5817_ = 3;
v___x_5818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5818_, 0, v___x_5816_);
lean_ctor_set_uint8(v___x_5818_, sizeof(void*)*1, v___x_5817_);
v___x_5819_ = lean_array_get_size(v_log_5801_);
v___x_5820_ = lean_array_push(v_log_5801_, v___x_5818_);
if (v_isShared_5808_ == 0)
{
lean_ctor_set(v___x_5807_, 0, v___x_5820_);
v___x_5822_ = v___x_5807_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5820_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v_trace_5804_);
lean_ctor_set(v_reuseFailAlloc_5824_, 2, v_buildTime_5805_);
lean_ctor_set_uint8(v_reuseFailAlloc_5824_, sizeof(void*)*3, v_action_5802_);
lean_ctor_set_uint8(v_reuseFailAlloc_5824_, sizeof(void*)*3 + 1, v_wantsRebuild_5803_);
v___x_5822_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
lean_object* v___x_5823_; 
v___x_5823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5819_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
return v___x_5823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec(v___y_5829_);
lean_dec(v___y_5828_);
lean_dec_ref(v___y_5827_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_){
_start:
{
lean_object* v___f_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___f_5843_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5843_, 0, v_path_5836_);
v___x_5844_ = l_Lake_instDataKindFilePath;
v___x_5845_ = lean_unsigned_to_nat(0u);
v___x_5846_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5847_ = l_Lake_Job_async___redArg(v___x_5844_, v___f_5843_, v___x_5845_, v___x_5846_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lake_inputBinFile___redArg(v_path_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_);
lean_dec_ref(v_a_5853_);
lean_dec(v_a_5852_);
lean_dec(v_a_5851_);
lean_dec(v_a_5850_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lake_inputBinFile___redArg(v_path_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_){
_start:
{
lean_object* v_res_5873_; 
v_res_5873_ = l_Lake_inputBinFile(v_path_5865_, v_a_5866_, v_a_5867_, v_a_5868_, v_a_5869_, v_a_5870_, v_a_5871_);
lean_dec_ref(v_a_5871_);
lean_dec_ref(v_a_5870_);
lean_dec(v_a_5869_);
lean_dec(v_a_5868_);
lean_dec(v_a_5867_);
return v_res_5873_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5874_){
_start:
{
lean_object* v___x_5876_; 
v___x_5876_ = l_Lake_computeTextFileHash(v_info_5874_);
if (lean_obj_tag(v___x_5876_) == 0)
{
lean_object* v_a_5877_; lean_object* v___x_5878_; 
v_a_5877_ = lean_ctor_get(v___x_5876_, 0);
lean_inc(v_a_5877_);
lean_dec_ref_known(v___x_5876_, 1);
v___x_5878_ = lean_io_metadata(v_info_5874_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5890_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5881_ = v___x_5878_;
v_isShared_5882_ = v_isSharedCheck_5890_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5878_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5890_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v_modified_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; uint64_t v___x_5886_; lean_object* v___x_5888_; 
v_modified_5883_ = lean_ctor_get(v_a_5879_, 1);
lean_inc_ref(v_modified_5883_);
lean_dec(v_a_5879_);
v___x_5884_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5885_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5885_, 0, v_info_5874_);
lean_ctor_set(v___x_5885_, 1, v___x_5884_);
lean_ctor_set(v___x_5885_, 2, v_modified_5883_);
v___x_5886_ = lean_unbox_uint64(v_a_5877_);
lean_dec(v_a_5877_);
lean_ctor_set_uint64(v___x_5885_, sizeof(void*)*3, v___x_5886_);
if (v_isShared_5882_ == 0)
{
lean_ctor_set(v___x_5881_, 0, v___x_5885_);
v___x_5888_ = v___x_5881_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v___x_5885_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_dec(v_a_5877_);
lean_dec_ref(v_info_5874_);
v_a_5891_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5878_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5878_);
v___x_5893_ = lean_box(0);
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
v_resetjp_5892_:
{
lean_object* v___x_5896_; 
if (v_isShared_5894_ == 0)
{
v___x_5896_ = v___x_5893_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_a_5891_);
v___x_5896_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
return v___x_5896_;
}
}
}
}
else
{
lean_object* v_a_5899_; lean_object* v___x_5901_; uint8_t v_isShared_5902_; uint8_t v_isSharedCheck_5906_; 
lean_dec_ref(v_info_5874_);
v_a_5899_ = lean_ctor_get(v___x_5876_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5876_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5901_ = v___x_5876_;
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
else
{
lean_inc(v_a_5899_);
lean_dec(v___x_5876_);
v___x_5901_ = lean_box(0);
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
v_resetjp_5900_:
{
lean_object* v___x_5904_; 
if (v_isShared_5902_ == 0)
{
v___x_5904_ = v___x_5901_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
v___x_5904_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
return v___x_5904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5907_, lean_object* v_a_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5907_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_){
_start:
{
lean_object* v_log_5918_; uint8_t v_action_5919_; uint8_t v_wantsRebuild_5920_; lean_object* v_trace_5921_; lean_object* v_buildTime_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5942_; 
v_log_5918_ = lean_ctor_get(v___y_5916_, 0);
v_action_5919_ = lean_ctor_get_uint8(v___y_5916_, sizeof(void*)*3);
v_wantsRebuild_5920_ = lean_ctor_get_uint8(v___y_5916_, sizeof(void*)*3 + 1);
v_trace_5921_ = lean_ctor_get(v___y_5916_, 1);
v_buildTime_5922_ = lean_ctor_get(v___y_5916_, 2);
v_isSharedCheck_5942_ = !lean_is_exclusive(v___y_5916_);
if (v_isSharedCheck_5942_ == 0)
{
v___x_5924_ = v___y_5916_;
v_isShared_5925_ = v_isSharedCheck_5942_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_buildTime_5922_);
lean_inc(v_trace_5921_);
lean_inc(v_log_5918_);
lean_dec(v___y_5916_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5942_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v___x_5926_; 
lean_inc_ref(v_path_5910_);
v___x_5926_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5910_);
if (lean_obj_tag(v___x_5926_) == 0)
{
lean_object* v_a_5927_; lean_object* v___x_5929_; 
lean_dec_ref(v_trace_5921_);
v_a_5927_ = lean_ctor_get(v___x_5926_, 0);
lean_inc(v_a_5927_);
lean_dec_ref_known(v___x_5926_, 1);
if (v_isShared_5925_ == 0)
{
lean_ctor_set(v___x_5924_, 1, v_a_5927_);
v___x_5929_ = v___x_5924_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_log_5918_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_a_5927_);
lean_ctor_set(v_reuseFailAlloc_5931_, 2, v_buildTime_5922_);
lean_ctor_set_uint8(v_reuseFailAlloc_5931_, sizeof(void*)*3, v_action_5919_);
lean_ctor_set_uint8(v_reuseFailAlloc_5931_, sizeof(void*)*3 + 1, v_wantsRebuild_5920_);
v___x_5929_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
lean_object* v___x_5930_; 
v___x_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5930_, 0, v_path_5910_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
return v___x_5930_;
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5939_; 
lean_dec_ref(v_path_5910_);
v_a_5932_ = lean_ctor_get(v___x_5926_, 0);
lean_inc(v_a_5932_);
lean_dec_ref_known(v___x_5926_, 1);
v___x_5933_ = lean_io_error_to_string(v_a_5932_);
v___x_5934_ = 3;
v___x_5935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5934_);
v___x_5936_ = lean_array_get_size(v_log_5918_);
v___x_5937_ = lean_array_push(v_log_5918_, v___x_5935_);
if (v_isShared_5925_ == 0)
{
lean_ctor_set(v___x_5924_, 0, v___x_5937_);
v___x_5939_ = v___x_5924_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5941_, 1, v_trace_5921_);
lean_ctor_set(v_reuseFailAlloc_5941_, 2, v_buildTime_5922_);
lean_ctor_set_uint8(v_reuseFailAlloc_5941_, sizeof(void*)*3, v_action_5919_);
lean_ctor_set_uint8(v_reuseFailAlloc_5941_, sizeof(void*)*3 + 1, v_wantsRebuild_5920_);
v___x_5939_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
lean_object* v___x_5940_; 
v___x_5940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5936_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
return v___x_5940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_){
_start:
{
lean_object* v_res_5951_; 
v_res_5951_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec(v___y_5946_);
lean_dec(v___y_5945_);
lean_dec_ref(v___y_5944_);
return v_res_5951_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_){
_start:
{
lean_object* v___f_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; 
v___f_5959_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5959_, 0, v_path_5952_);
v___x_5960_ = l_Lake_instDataKindFilePath;
v___x_5961_ = lean_unsigned_to_nat(0u);
v___x_5962_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5963_ = l_Lake_Job_async___redArg(v___x_5960_, v___f_5959_, v___x_5961_, v___x_5962_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
return v___x_5963_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_){
_start:
{
lean_object* v_res_5971_; 
v_res_5971_ = l_Lake_inputTextFile___redArg(v_path_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec(v_a_5967_);
lean_dec(v_a_5966_);
return v_res_5971_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_){
_start:
{
lean_object* v___x_5980_; 
v___x_5980_ = l_Lake_inputTextFile___redArg(v_path_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_, v_a_5977_);
return v___x_5980_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_){
_start:
{
lean_object* v_res_5989_; 
v_res_5989_ = l_Lake_inputTextFile(v_path_5981_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
lean_dec_ref(v_a_5987_);
lean_dec_ref(v_a_5986_);
lean_dec(v_a_5985_);
lean_dec(v_a_5984_);
lean_dec(v_a_5983_);
return v_res_5989_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5990_, uint8_t v_text_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
if (v_text_5991_ == 0)
{
lean_object* v___x_5998_; 
v___x_5998_ = l_Lake_inputBinFile___redArg(v_path_5990_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_);
return v___x_5998_;
}
else
{
lean_object* v___x_5999_; 
v___x_5999_ = l_Lake_inputTextFile___redArg(v_path_5990_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_);
return v___x_5999_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_6000_, lean_object* v_text_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_){
_start:
{
uint8_t v_text_boxed_6008_; lean_object* v_res_6009_; 
v_text_boxed_6008_ = lean_unbox(v_text_6001_);
v_res_6009_ = l_Lake_inputFile___redArg(v_path_6000_, v_text_boxed_6008_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_);
lean_dec_ref(v_a_6006_);
lean_dec(v_a_6005_);
lean_dec(v_a_6004_);
lean_dec(v_a_6003_);
return v_res_6009_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_6010_, uint8_t v_text_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_){
_start:
{
if (v_text_6011_ == 0)
{
lean_object* v___x_6019_; 
v___x_6019_ = l_Lake_inputBinFile___redArg(v_path_6010_, v_a_6012_, v_a_6013_, v_a_6014_, v_a_6015_, v_a_6016_);
return v___x_6019_;
}
else
{
lean_object* v___x_6020_; 
v___x_6020_ = l_Lake_inputTextFile___redArg(v_path_6010_, v_a_6012_, v_a_6013_, v_a_6014_, v_a_6015_, v_a_6016_);
return v___x_6020_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_6021_, lean_object* v_text_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_){
_start:
{
uint8_t v_text_boxed_6030_; lean_object* v_res_6031_; 
v_text_boxed_6030_ = lean_unbox(v_text_6022_);
v_res_6031_ = l_Lake_inputFile(v_path_6021_, v_text_boxed_6030_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_, v_a_6028_);
lean_dec_ref(v_a_6028_);
lean_dec_ref(v_a_6027_);
lean_dec(v_a_6026_);
lean_dec(v_a_6025_);
lean_dec(v_a_6024_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6032_){
_start:
{
uint8_t v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6034_ = 1;
v___x_6035_ = lean_box(v___x_6034_);
v___x_6036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
return v___x_6036_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6037_, lean_object* v___y_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_Lake_inputDir___lam__0(v_x_6037_);
lean_dec_ref(v_x_6037_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6040_, lean_object* v_as_6041_, size_t v_i_6042_, size_t v_stop_6043_, lean_object* v_b_6044_, lean_object* v___y_6045_){
_start:
{
lean_object* v_a_6048_; lean_object* v_a_6049_; uint8_t v___x_6053_; 
v___x_6053_ = lean_usize_dec_eq(v_i_6042_, v_stop_6043_);
if (v___x_6053_ == 0)
{
lean_object* v___x_6054_; uint8_t v___x_6055_; uint8_t v___y_6057_; uint8_t v___x_6059_; 
v___x_6054_ = lean_array_uget_borrowed(v_as_6041_, v_i_6042_);
v___x_6055_ = l_System_FilePath_isDir(v___x_6054_);
v___x_6059_ = lean_bool_not(v___x_6055_);
if (v___x_6059_ == 0)
{
v___y_6057_ = v___x_6059_;
goto v___jp_6056_;
}
else
{
lean_object* v___x_6060_; uint8_t v___x_6061_; 
lean_inc_ref(v_filter_6040_);
lean_inc(v___x_6054_);
v___x_6060_ = lean_apply_1(v_filter_6040_, v___x_6054_);
v___x_6061_ = lean_unbox(v___x_6060_);
v___y_6057_ = v___x_6061_;
goto v___jp_6056_;
}
v___jp_6056_:
{
if (v___y_6057_ == 0)
{
v_a_6048_ = v_b_6044_;
v_a_6049_ = v___y_6045_;
goto v___jp_6047_;
}
else
{
lean_object* v___x_6058_; 
lean_inc(v___x_6054_);
v___x_6058_ = lean_array_push(v_b_6044_, v___x_6054_);
v_a_6048_ = v___x_6058_;
v_a_6049_ = v___y_6045_;
goto v___jp_6047_;
}
}
}
else
{
lean_object* v___x_6062_; 
lean_dec_ref(v_filter_6040_);
v___x_6062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6062_, 0, v_b_6044_);
lean_ctor_set(v___x_6062_, 1, v___y_6045_);
return v___x_6062_;
}
v___jp_6047_:
{
size_t v___x_6050_; size_t v___x_6051_; 
v___x_6050_ = ((size_t)1ULL);
v___x_6051_ = lean_usize_add(v_i_6042_, v___x_6050_);
v_i_6042_ = v___x_6051_;
v_b_6044_ = v_a_6048_;
v___y_6045_ = v_a_6049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6063_, lean_object* v_as_6064_, lean_object* v_i_6065_, lean_object* v_stop_6066_, lean_object* v_b_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
size_t v_i_boxed_6070_; size_t v_stop_boxed_6071_; lean_object* v_res_6072_; 
v_i_boxed_6070_ = lean_unbox_usize(v_i_6065_);
lean_dec(v_i_6065_);
v_stop_boxed_6071_ = lean_unbox_usize(v_stop_6066_);
lean_dec(v_stop_6066_);
v_res_6072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6063_, v_as_6064_, v_i_boxed_6070_, v_stop_boxed_6071_, v_b_6067_, v___y_6068_);
lean_dec_ref(v_as_6064_);
return v_res_6072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6073_, lean_object* v_pivot_6074_, lean_object* v_as_6075_, lean_object* v_i_6076_, lean_object* v_k_6077_){
_start:
{
uint8_t v___x_6078_; 
v___x_6078_ = lean_nat_dec_lt(v_k_6077_, v_hi_6073_);
if (v___x_6078_ == 0)
{
lean_object* v___x_6079_; lean_object* v___x_6080_; 
lean_dec(v_k_6077_);
v___x_6079_ = lean_array_fswap(v_as_6075_, v_i_6076_, v_hi_6073_);
v___x_6080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6080_, 0, v_i_6076_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
return v___x_6080_;
}
else
{
lean_object* v___x_6081_; uint8_t v___x_6082_; 
v___x_6081_ = lean_array_fget_borrowed(v_as_6075_, v_k_6077_);
v___x_6082_ = lean_string_dec_lt(v___x_6081_, v_pivot_6074_);
if (v___x_6082_ == 0)
{
lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6083_ = lean_unsigned_to_nat(1u);
v___x_6084_ = lean_nat_add(v_k_6077_, v___x_6083_);
lean_dec(v_k_6077_);
v_k_6077_ = v___x_6084_;
goto _start;
}
else
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; 
v___x_6086_ = lean_array_fswap(v_as_6075_, v_i_6076_, v_k_6077_);
v___x_6087_ = lean_unsigned_to_nat(1u);
v___x_6088_ = lean_nat_add(v_i_6076_, v___x_6087_);
lean_dec(v_i_6076_);
v___x_6089_ = lean_nat_add(v_k_6077_, v___x_6087_);
lean_dec(v_k_6077_);
v_as_6075_ = v___x_6086_;
v_i_6076_ = v___x_6088_;
v_k_6077_ = v___x_6089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6091_, lean_object* v_pivot_6092_, lean_object* v_as_6093_, lean_object* v_i_6094_, lean_object* v_k_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6091_, v_pivot_6092_, v_as_6093_, v_i_6094_, v_k_6095_);
lean_dec_ref(v_pivot_6092_);
lean_dec(v_hi_6091_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6097_, lean_object* v_as_6098_, lean_object* v_lo_6099_, lean_object* v_hi_6100_){
_start:
{
lean_object* v___y_6102_; uint8_t v___x_6112_; 
v___x_6112_ = lean_nat_dec_lt(v_lo_6099_, v_hi_6100_);
if (v___x_6112_ == 0)
{
lean_dec(v_lo_6099_);
return v_as_6098_;
}
else
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v_mid_6115_; lean_object* v___y_6117_; lean_object* v___y_6123_; lean_object* v___x_6128_; lean_object* v___x_6129_; uint8_t v___x_6130_; 
v___x_6113_ = lean_nat_add(v_lo_6099_, v_hi_6100_);
v___x_6114_ = lean_unsigned_to_nat(1u);
v_mid_6115_ = lean_nat_shiftr(v___x_6113_, v___x_6114_);
lean_dec(v___x_6113_);
v___x_6128_ = lean_array_fget_borrowed(v_as_6098_, v_mid_6115_);
v___x_6129_ = lean_array_fget_borrowed(v_as_6098_, v_lo_6099_);
v___x_6130_ = lean_string_dec_lt(v___x_6128_, v___x_6129_);
if (v___x_6130_ == 0)
{
v___y_6123_ = v_as_6098_;
goto v___jp_6122_;
}
else
{
lean_object* v___x_6131_; 
v___x_6131_ = lean_array_fswap(v_as_6098_, v_lo_6099_, v_mid_6115_);
v___y_6123_ = v___x_6131_;
goto v___jp_6122_;
}
v___jp_6116_:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; uint8_t v___x_6120_; 
v___x_6118_ = lean_array_fget_borrowed(v___y_6117_, v_mid_6115_);
v___x_6119_ = lean_array_fget_borrowed(v___y_6117_, v_hi_6100_);
v___x_6120_ = lean_string_dec_lt(v___x_6118_, v___x_6119_);
if (v___x_6120_ == 0)
{
lean_dec(v_mid_6115_);
v___y_6102_ = v___y_6117_;
goto v___jp_6101_;
}
else
{
lean_object* v___x_6121_; 
v___x_6121_ = lean_array_fswap(v___y_6117_, v_mid_6115_, v_hi_6100_);
lean_dec(v_mid_6115_);
v___y_6102_ = v___x_6121_;
goto v___jp_6101_;
}
}
v___jp_6122_:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; uint8_t v___x_6126_; 
v___x_6124_ = lean_array_fget_borrowed(v___y_6123_, v_hi_6100_);
v___x_6125_ = lean_array_fget_borrowed(v___y_6123_, v_lo_6099_);
v___x_6126_ = lean_string_dec_lt(v___x_6124_, v___x_6125_);
if (v___x_6126_ == 0)
{
v___y_6117_ = v___y_6123_;
goto v___jp_6116_;
}
else
{
lean_object* v___x_6127_; 
v___x_6127_ = lean_array_fswap(v___y_6123_, v_lo_6099_, v_hi_6100_);
v___y_6117_ = v___x_6127_;
goto v___jp_6116_;
}
}
}
v___jp_6101_:
{
lean_object* v_pivot_6103_; lean_object* v___x_6104_; lean_object* v_fst_6105_; lean_object* v_snd_6106_; uint8_t v___x_6107_; 
v_pivot_6103_ = lean_array_fget(v___y_6102_, v_hi_6100_);
lean_inc_n(v_lo_6099_, 2);
v___x_6104_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6100_, v_pivot_6103_, v___y_6102_, v_lo_6099_, v_lo_6099_);
lean_dec(v_pivot_6103_);
v_fst_6105_ = lean_ctor_get(v___x_6104_, 0);
lean_inc(v_fst_6105_);
v_snd_6106_ = lean_ctor_get(v___x_6104_, 1);
lean_inc(v_snd_6106_);
lean_dec_ref(v___x_6104_);
v___x_6107_ = lean_nat_dec_le(v_hi_6100_, v_fst_6105_);
if (v___x_6107_ == 0)
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6097_, v_snd_6106_, v_lo_6099_, v_fst_6105_);
v___x_6109_ = lean_unsigned_to_nat(1u);
v___x_6110_ = lean_nat_add(v_fst_6105_, v___x_6109_);
lean_dec(v_fst_6105_);
v_as_6098_ = v___x_6108_;
v_lo_6099_ = v___x_6110_;
goto _start;
}
else
{
lean_dec(v_fst_6105_);
lean_dec(v_lo_6099_);
return v_snd_6106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6132_, lean_object* v_as_6133_, lean_object* v_lo_6134_, lean_object* v_hi_6135_){
_start:
{
lean_object* v_res_6136_; 
v_res_6136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6132_, v_as_6133_, v_lo_6134_, v_hi_6135_);
lean_dec(v_hi_6135_);
lean_dec(v_n_6132_);
return v_res_6136_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6139_, lean_object* v___f_6140_, lean_object* v_filter_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_){
_start:
{
lean_object* v___y_6150_; lean_object* v___y_6151_; lean_object* v___y_6154_; lean_object* v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6158_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v_log_6167_; uint8_t v_action_6168_; uint8_t v_wantsRebuild_6169_; lean_object* v_trace_6170_; lean_object* v_buildTime_6171_; lean_object* v___x_6172_; 
v_log_6167_ = lean_ctor_get(v___y_6147_, 0);
v_action_6168_ = lean_ctor_get_uint8(v___y_6147_, sizeof(void*)*3);
v_wantsRebuild_6169_ = lean_ctor_get_uint8(v___y_6147_, sizeof(void*)*3 + 1);
v_trace_6170_ = lean_ctor_get(v___y_6147_, 1);
v_buildTime_6171_ = lean_ctor_get(v___y_6147_, 2);
v___x_6172_ = l_System_FilePath_walkDir(v_path_6139_, v___f_6140_);
if (lean_obj_tag(v___x_6172_) == 0)
{
lean_object* v_a_6173_; lean_object* v___x_6174_; lean_object* v_a_6176_; lean_object* v_a_6177_; lean_object* v___y_6184_; lean_object* v___x_6187_; lean_object* v___x_6188_; uint8_t v___x_6189_; 
v_a_6173_ = lean_ctor_get(v___x_6172_, 0);
lean_inc(v_a_6173_);
lean_dec_ref_known(v___x_6172_, 1);
v___x_6174_ = lean_unsigned_to_nat(0u);
v___x_6187_ = lean_array_get_size(v_a_6173_);
v___x_6188_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6189_ = lean_nat_dec_lt(v___x_6174_, v___x_6187_);
if (v___x_6189_ == 0)
{
lean_dec(v_a_6173_);
lean_dec_ref(v_filter_6141_);
v_a_6176_ = v___x_6188_;
v_a_6177_ = v___y_6147_;
goto v___jp_6175_;
}
else
{
uint8_t v___x_6190_; 
v___x_6190_ = lean_nat_dec_le(v___x_6187_, v___x_6187_);
if (v___x_6190_ == 0)
{
if (v___x_6189_ == 0)
{
lean_dec(v_a_6173_);
lean_dec_ref(v_filter_6141_);
v_a_6176_ = v___x_6188_;
v_a_6177_ = v___y_6147_;
goto v___jp_6175_;
}
else
{
size_t v___x_6191_; size_t v___x_6192_; lean_object* v___x_6193_; 
v___x_6191_ = ((size_t)0ULL);
v___x_6192_ = lean_usize_of_nat(v___x_6187_);
v___x_6193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6141_, v_a_6173_, v___x_6191_, v___x_6192_, v___x_6188_, v___y_6147_);
lean_dec(v_a_6173_);
v___y_6184_ = v___x_6193_;
goto v___jp_6183_;
}
}
else
{
size_t v___x_6194_; size_t v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = ((size_t)0ULL);
v___x_6195_ = lean_usize_of_nat(v___x_6187_);
v___x_6196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6141_, v_a_6173_, v___x_6194_, v___x_6195_, v___x_6188_, v___y_6147_);
lean_dec(v_a_6173_);
v___y_6184_ = v___x_6196_;
goto v___jp_6183_;
}
}
v___jp_6175_:
{
lean_object* v___x_6178_; uint8_t v___x_6179_; 
v___x_6178_ = lean_array_get_size(v_a_6176_);
v___x_6179_ = lean_nat_dec_eq(v___x_6178_, v___x_6174_);
if (v___x_6179_ == 0)
{
lean_object* v___x_6180_; lean_object* v___x_6181_; uint8_t v___x_6182_; 
v___x_6180_ = lean_unsigned_to_nat(1u);
v___x_6181_ = lean_nat_sub(v___x_6178_, v___x_6180_);
v___x_6182_ = lean_nat_dec_le(v___x_6174_, v___x_6181_);
if (v___x_6182_ == 0)
{
lean_inc(v___x_6181_);
v___y_6161_ = v___x_6178_;
v___y_6162_ = v_a_6177_;
v___y_6163_ = v___x_6181_;
v___y_6164_ = v_a_6176_;
v___y_6165_ = v___x_6181_;
goto v___jp_6160_;
}
else
{
v___y_6161_ = v___x_6178_;
v___y_6162_ = v_a_6177_;
v___y_6163_ = v___x_6181_;
v___y_6164_ = v_a_6176_;
v___y_6165_ = v___x_6174_;
goto v___jp_6160_;
}
}
else
{
v___y_6150_ = v_a_6177_;
v___y_6151_ = v_a_6176_;
goto v___jp_6149_;
}
}
v___jp_6183_:
{
if (lean_obj_tag(v___y_6184_) == 0)
{
lean_object* v_a_6185_; lean_object* v_a_6186_; 
v_a_6185_ = lean_ctor_get(v___y_6184_, 0);
lean_inc(v_a_6185_);
v_a_6186_ = lean_ctor_get(v___y_6184_, 1);
lean_inc(v_a_6186_);
lean_dec_ref_known(v___y_6184_, 2);
v_a_6176_ = v_a_6185_;
v_a_6177_ = v_a_6186_;
goto v___jp_6175_;
}
else
{
return v___y_6184_;
}
}
}
else
{
lean_object* v___x_6198_; uint8_t v_isShared_6199_; uint8_t v_isSharedCheck_6210_; 
lean_inc(v_buildTime_6171_);
lean_inc_ref(v_trace_6170_);
lean_inc_ref(v_log_6167_);
lean_dec_ref(v_filter_6141_);
v_isSharedCheck_6210_ = !lean_is_exclusive(v___y_6147_);
if (v_isSharedCheck_6210_ == 0)
{
lean_object* v_unused_6211_; lean_object* v_unused_6212_; lean_object* v_unused_6213_; 
v_unused_6211_ = lean_ctor_get(v___y_6147_, 2);
lean_dec(v_unused_6211_);
v_unused_6212_ = lean_ctor_get(v___y_6147_, 1);
lean_dec(v_unused_6212_);
v_unused_6213_ = lean_ctor_get(v___y_6147_, 0);
lean_dec(v_unused_6213_);
v___x_6198_ = v___y_6147_;
v_isShared_6199_ = v_isSharedCheck_6210_;
goto v_resetjp_6197_;
}
else
{
lean_dec(v___y_6147_);
v___x_6198_ = lean_box(0);
v_isShared_6199_ = v_isSharedCheck_6210_;
goto v_resetjp_6197_;
}
v_resetjp_6197_:
{
lean_object* v_a_6200_; lean_object* v___x_6201_; uint8_t v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6207_; 
v_a_6200_ = lean_ctor_get(v___x_6172_, 0);
lean_inc(v_a_6200_);
lean_dec_ref_known(v___x_6172_, 1);
v___x_6201_ = lean_io_error_to_string(v_a_6200_);
v___x_6202_ = 3;
v___x_6203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6203_, 0, v___x_6201_);
lean_ctor_set_uint8(v___x_6203_, sizeof(void*)*1, v___x_6202_);
v___x_6204_ = lean_array_get_size(v_log_6167_);
v___x_6205_ = lean_array_push(v_log_6167_, v___x_6203_);
if (v_isShared_6199_ == 0)
{
lean_ctor_set(v___x_6198_, 0, v___x_6205_);
v___x_6207_ = v___x_6198_;
goto v_reusejp_6206_;
}
else
{
lean_object* v_reuseFailAlloc_6209_; 
v_reuseFailAlloc_6209_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6209_, 0, v___x_6205_);
lean_ctor_set(v_reuseFailAlloc_6209_, 1, v_trace_6170_);
lean_ctor_set(v_reuseFailAlloc_6209_, 2, v_buildTime_6171_);
lean_ctor_set_uint8(v_reuseFailAlloc_6209_, sizeof(void*)*3, v_action_6168_);
lean_ctor_set_uint8(v_reuseFailAlloc_6209_, sizeof(void*)*3 + 1, v_wantsRebuild_6169_);
v___x_6207_ = v_reuseFailAlloc_6209_;
goto v_reusejp_6206_;
}
v_reusejp_6206_:
{
lean_object* v___x_6208_; 
v___x_6208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6204_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
return v___x_6208_;
}
}
}
v___jp_6149_:
{
lean_object* v___x_6152_; 
v___x_6152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___y_6151_);
lean_ctor_set(v___x_6152_, 1, v___y_6150_);
return v___x_6152_;
}
v___jp_6153_:
{
lean_object* v___x_6159_; 
v___x_6159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6154_, v___y_6156_, v___y_6157_, v___y_6158_);
lean_dec(v___y_6158_);
lean_dec(v___y_6154_);
v___y_6150_ = v___y_6155_;
v___y_6151_ = v___x_6159_;
goto v___jp_6149_;
}
v___jp_6160_:
{
uint8_t v___x_6166_; 
v___x_6166_ = lean_nat_dec_le(v___y_6165_, v___y_6163_);
if (v___x_6166_ == 0)
{
lean_dec(v___y_6163_);
lean_inc(v___y_6165_);
v___y_6154_ = v___y_6161_;
v___y_6155_ = v___y_6162_;
v___y_6156_ = v___y_6164_;
v___y_6157_ = v___y_6165_;
v___y_6158_ = v___y_6165_;
goto v___jp_6153_;
}
else
{
v___y_6154_ = v___y_6161_;
v___y_6155_ = v___y_6162_;
v___y_6156_ = v___y_6164_;
v___y_6157_ = v___y_6165_;
v___y_6158_ = v___y_6163_;
goto v___jp_6153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6214_, lean_object* v___f_6215_, lean_object* v_filter_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_){
_start:
{
lean_object* v_res_6224_; 
v_res_6224_ = l_Lake_inputDir___lam__1(v_path_6214_, v___f_6215_, v_filter_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
lean_dec_ref(v___y_6221_);
lean_dec(v___y_6220_);
lean_dec(v___y_6219_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
return v_res_6224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6225_, size_t v_sz_6226_, size_t v_i_6227_, lean_object* v_bs_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
uint8_t v___x_6236_; 
v___x_6236_ = lean_usize_dec_lt(v_i_6227_, v_sz_6226_);
if (v___x_6236_ == 0)
{
lean_object* v___x_6237_; 
lean_dec_ref(v___y_6229_);
v___x_6237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6237_, 0, v_bs_6228_);
lean_ctor_set(v___x_6237_, 1, v___y_6234_);
return v___x_6237_;
}
else
{
lean_object* v_v_6238_; lean_object* v___x_6239_; lean_object* v_bs_x27_6240_; lean_object* v___y_6242_; 
v_v_6238_ = lean_array_uget(v_bs_6228_, v_i_6227_);
v___x_6239_ = lean_unsigned_to_nat(0u);
v_bs_x27_6240_ = lean_array_uset(v_bs_6228_, v_i_6227_, v___x_6239_);
if (v_text_6225_ == 0)
{
lean_object* v___x_6247_; 
lean_inc_ref(v___y_6229_);
v___x_6247_ = l_Lake_inputBinFile___redArg(v_v_6238_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
v___y_6242_ = v___x_6247_;
goto v___jp_6241_;
}
else
{
lean_object* v___x_6248_; 
lean_inc_ref(v___y_6229_);
v___x_6248_ = l_Lake_inputTextFile___redArg(v_v_6238_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
v___y_6242_ = v___x_6248_;
goto v___jp_6241_;
}
v___jp_6241_:
{
size_t v___x_6243_; size_t v___x_6244_; lean_object* v___x_6245_; 
v___x_6243_ = ((size_t)1ULL);
v___x_6244_ = lean_usize_add(v_i_6227_, v___x_6243_);
v___x_6245_ = lean_array_uset(v_bs_x27_6240_, v_i_6227_, v___y_6242_);
v_i_6227_ = v___x_6244_;
v_bs_6228_ = v___x_6245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6249_, lean_object* v_sz_6250_, lean_object* v_i_6251_, lean_object* v_bs_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_){
_start:
{
uint8_t v_text_boxed_6260_; size_t v_sz_boxed_6261_; size_t v_i_boxed_6262_; lean_object* v_res_6263_; 
v_text_boxed_6260_ = lean_unbox(v_text_6249_);
v_sz_boxed_6261_ = lean_unbox_usize(v_sz_6250_);
lean_dec(v_sz_6250_);
v_i_boxed_6262_ = lean_unbox_usize(v_i_6251_);
lean_dec(v_i_6251_);
v_res_6263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6260_, v_sz_boxed_6261_, v_i_boxed_6262_, v_bs_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_);
lean_dec_ref(v___y_6257_);
lean_dec(v___y_6256_);
lean_dec(v___y_6255_);
lean_dec(v___y_6254_);
return v_res_6263_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6264_, lean_object* v_path_6265_, lean_object* v_ps_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_){
_start:
{
size_t v_sz_6274_; size_t v___x_6275_; lean_object* v___x_6276_; 
v_sz_6274_ = lean_array_size(v_ps_6266_);
v___x_6275_ = ((size_t)0ULL);
v___x_6276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6264_, v_sz_6274_, v___x_6275_, v_ps_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
if (lean_obj_tag(v___x_6276_) == 0)
{
lean_object* v_a_6277_; lean_object* v_a_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6286_; 
v_a_6277_ = lean_ctor_get(v___x_6276_, 0);
v_a_6278_ = lean_ctor_get(v___x_6276_, 1);
v_isSharedCheck_6286_ = !lean_is_exclusive(v___x_6276_);
if (v_isSharedCheck_6286_ == 0)
{
v___x_6280_ = v___x_6276_;
v_isShared_6281_ = v_isSharedCheck_6286_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_a_6278_);
lean_inc(v_a_6277_);
lean_dec(v___x_6276_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6286_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v___x_6282_; lean_object* v___x_6284_; 
v___x_6282_ = l_Lake_Job_collectArray___redArg(v_a_6277_, v_path_6265_);
lean_dec(v_a_6277_);
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v___x_6282_);
v___x_6284_ = v___x_6280_;
goto v_reusejp_6283_;
}
else
{
lean_object* v_reuseFailAlloc_6285_; 
v_reuseFailAlloc_6285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6285_, 0, v___x_6282_);
lean_ctor_set(v_reuseFailAlloc_6285_, 1, v_a_6278_);
v___x_6284_ = v_reuseFailAlloc_6285_;
goto v_reusejp_6283_;
}
v_reusejp_6283_:
{
return v___x_6284_;
}
}
}
else
{
lean_object* v_a_6287_; lean_object* v_a_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6295_; 
lean_dec_ref(v_path_6265_);
v_a_6287_ = lean_ctor_get(v___x_6276_, 0);
v_a_6288_ = lean_ctor_get(v___x_6276_, 1);
v_isSharedCheck_6295_ = !lean_is_exclusive(v___x_6276_);
if (v_isSharedCheck_6295_ == 0)
{
v___x_6290_ = v___x_6276_;
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
else
{
lean_inc(v_a_6288_);
lean_inc(v_a_6287_);
lean_dec(v___x_6276_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6293_; 
if (v_isShared_6291_ == 0)
{
v___x_6293_ = v___x_6290_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_a_6287_);
lean_ctor_set(v_reuseFailAlloc_6294_, 1, v_a_6288_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6296_, lean_object* v_path_6297_, lean_object* v_ps_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
uint8_t v_text_boxed_6306_; lean_object* v_res_6307_; 
v_text_boxed_6306_ = lean_unbox(v_text_6296_);
v_res_6307_ = l_Lake_inputDir___lam__2(v_text_boxed_6306_, v_path_6297_, v_ps_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
lean_dec_ref(v___y_6303_);
lean_dec(v___y_6302_);
lean_dec(v___y_6301_);
lean_dec(v___y_6300_);
return v_res_6307_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6309_, uint8_t v_text_6310_, lean_object* v_filter_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_){
_start:
{
lean_object* v___f_6319_; lean_object* v___f_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___f_6326_; uint8_t v___x_6327_; lean_object* v___x_6328_; 
v___f_6319_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6309_);
v___f_6320_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6320_, 0, v_path_6309_);
lean_closure_set(v___f_6320_, 1, v___f_6319_);
lean_closure_set(v___f_6320_, 2, v_filter_6311_);
v___x_6321_ = lean_box(0);
v___x_6322_ = lean_unsigned_to_nat(0u);
v___x_6323_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6312_);
v___x_6324_ = l_Lake_Job_async___redArg(v___x_6321_, v___f_6320_, v___x_6322_, v___x_6323_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_);
v___x_6325_ = lean_box(v_text_6310_);
v___f_6326_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6326_, 0, v___x_6325_);
lean_closure_set(v___f_6326_, 1, v_path_6309_);
v___x_6327_ = 0;
v___x_6328_ = l_Lake_Job_bindM___redArg(v___x_6321_, v___x_6324_, v___f_6326_, v___x_6322_, v___x_6327_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_);
return v___x_6328_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6329_, lean_object* v_text_6330_, lean_object* v_filter_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_){
_start:
{
uint8_t v_text_boxed_6339_; lean_object* v_res_6340_; 
v_text_boxed_6339_ = lean_unbox(v_text_6330_);
v_res_6340_ = l_Lake_inputDir(v_path_6329_, v_text_boxed_6339_, v_filter_6331_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_);
lean_dec_ref(v_a_6337_);
lean_dec_ref(v_a_6336_);
lean_dec(v_a_6335_);
lean_dec(v_a_6334_);
lean_dec(v_a_6333_);
return v_res_6340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6341_, lean_object* v_as_6342_, lean_object* v_lo_6343_, lean_object* v_hi_6344_, lean_object* v_w_6345_, lean_object* v_hlo_6346_, lean_object* v_hhi_6347_){
_start:
{
lean_object* v___x_6348_; 
v___x_6348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6341_, v_as_6342_, v_lo_6343_, v_hi_6344_);
return v___x_6348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6349_, lean_object* v_as_6350_, lean_object* v_lo_6351_, lean_object* v_hi_6352_, lean_object* v_w_6353_, lean_object* v_hlo_6354_, lean_object* v_hhi_6355_){
_start:
{
lean_object* v_res_6356_; 
v_res_6356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6349_, v_as_6350_, v_lo_6351_, v_hi_6352_, v_w_6353_, v_hlo_6354_, v_hhi_6355_);
lean_dec(v_hi_6352_);
lean_dec(v_n_6349_);
return v_res_6356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6357_, lean_object* v_as_6358_, size_t v_i_6359_, size_t v_stop_6360_, lean_object* v_b_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_){
_start:
{
lean_object* v___x_6369_; 
v___x_6369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6357_, v_as_6358_, v_i_6359_, v_stop_6360_, v_b_6361_, v___y_6367_);
return v___x_6369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6370_, lean_object* v_as_6371_, lean_object* v_i_6372_, lean_object* v_stop_6373_, lean_object* v_b_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_){
_start:
{
size_t v_i_boxed_6382_; size_t v_stop_boxed_6383_; lean_object* v_res_6384_; 
v_i_boxed_6382_ = lean_unbox_usize(v_i_6372_);
lean_dec(v_i_6372_);
v_stop_boxed_6383_ = lean_unbox_usize(v_stop_6373_);
lean_dec(v_stop_6373_);
v_res_6384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6370_, v_as_6371_, v_i_boxed_6382_, v_stop_boxed_6383_, v_b_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_);
lean_dec_ref(v___y_6379_);
lean_dec(v___y_6378_);
lean_dec(v___y_6377_);
lean_dec(v___y_6376_);
lean_dec_ref(v___y_6375_);
lean_dec_ref(v_as_6371_);
return v_res_6384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6385_, lean_object* v_lo_6386_, lean_object* v_hi_6387_, lean_object* v_hhi_6388_, lean_object* v_pivot_6389_, lean_object* v_as_6390_, lean_object* v_i_6391_, lean_object* v_k_6392_, lean_object* v_ilo_6393_, lean_object* v_ik_6394_, lean_object* v_w_6395_){
_start:
{
lean_object* v___x_6396_; 
v___x_6396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6387_, v_pivot_6389_, v_as_6390_, v_i_6391_, v_k_6392_);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6397_, lean_object* v_lo_6398_, lean_object* v_hi_6399_, lean_object* v_hhi_6400_, lean_object* v_pivot_6401_, lean_object* v_as_6402_, lean_object* v_i_6403_, lean_object* v_k_6404_, lean_object* v_ilo_6405_, lean_object* v_ik_6406_, lean_object* v_w_6407_){
_start:
{
lean_object* v_res_6408_; 
v_res_6408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6397_, v_lo_6398_, v_hi_6399_, v_hhi_6400_, v_pivot_6401_, v_as_6402_, v_i_6403_, v_k_6404_, v_ilo_6405_, v_ik_6406_, v_w_6407_);
lean_dec_ref(v_pivot_6401_);
lean_dec(v_hi_6399_);
lean_dec(v_lo_6398_);
lean_dec(v_n_6397_);
return v_res_6408_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6409_, lean_object* v_t_6410_){
_start:
{
uint64_t v___x_6411_; uint64_t v___x_6412_; uint64_t v___x_6413_; uint64_t v___x_6414_; 
v___x_6411_ = l_Lake_Hash_nil;
v___x_6412_ = lean_string_hash(v_t_6410_);
v___x_6413_ = lean_uint64_mix_hash(v___x_6411_, v___x_6412_);
v___x_6414_ = lean_uint64_mix_hash(v_ts_6409_, v___x_6413_);
return v___x_6414_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6415_, lean_object* v_t_6416_){
_start:
{
uint64_t v_ts_boxed_6417_; uint64_t v_res_6418_; lean_object* v_r_6419_; 
v_ts_boxed_6417_ = lean_unbox_uint64(v_ts_6415_);
lean_dec_ref(v_ts_6415_);
v_res_6418_ = l_Lake_buildO___lam__0(v_ts_boxed_6417_, v_t_6416_);
lean_dec_ref(v_t_6416_);
v_r_6419_ = lean_box_uint64(v_res_6418_);
return v_r_6419_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6420_, lean_object* v_srcFile_6421_, lean_object* v___x_6422_, lean_object* v_compiler_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_){
_start:
{
lean_object* v_log_6431_; uint8_t v_action_6432_; uint8_t v_wantsRebuild_6433_; lean_object* v_trace_6434_; lean_object* v_buildTime_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6464_; 
v_log_6431_ = lean_ctor_get(v___y_6429_, 0);
v_action_6432_ = lean_ctor_get_uint8(v___y_6429_, sizeof(void*)*3);
v_wantsRebuild_6433_ = lean_ctor_get_uint8(v___y_6429_, sizeof(void*)*3 + 1);
v_trace_6434_ = lean_ctor_get(v___y_6429_, 1);
v_buildTime_6435_ = lean_ctor_get(v___y_6429_, 2);
v_isSharedCheck_6464_ = !lean_is_exclusive(v___y_6429_);
if (v_isSharedCheck_6464_ == 0)
{
v___x_6437_ = v___y_6429_;
v_isShared_6438_ = v_isSharedCheck_6464_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_buildTime_6435_);
lean_inc(v_trace_6434_);
lean_inc(v_log_6431_);
lean_dec(v___y_6429_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6464_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
lean_object* v___x_6439_; 
v___x_6439_ = l_Lake_compileO(v_oFile_6420_, v_srcFile_6421_, v___x_6422_, v_compiler_6423_, v_log_6431_);
if (lean_obj_tag(v___x_6439_) == 0)
{
lean_object* v_a_6440_; lean_object* v_a_6441_; lean_object* v___x_6443_; uint8_t v_isShared_6444_; uint8_t v_isSharedCheck_6451_; 
v_a_6440_ = lean_ctor_get(v___x_6439_, 0);
v_a_6441_ = lean_ctor_get(v___x_6439_, 1);
v_isSharedCheck_6451_ = !lean_is_exclusive(v___x_6439_);
if (v_isSharedCheck_6451_ == 0)
{
v___x_6443_ = v___x_6439_;
v_isShared_6444_ = v_isSharedCheck_6451_;
goto v_resetjp_6442_;
}
else
{
lean_inc(v_a_6441_);
lean_inc(v_a_6440_);
lean_dec(v___x_6439_);
v___x_6443_ = lean_box(0);
v_isShared_6444_ = v_isSharedCheck_6451_;
goto v_resetjp_6442_;
}
v_resetjp_6442_:
{
lean_object* v___x_6446_; 
if (v_isShared_6438_ == 0)
{
lean_ctor_set(v___x_6437_, 0, v_a_6441_);
v___x_6446_ = v___x_6437_;
goto v_reusejp_6445_;
}
else
{
lean_object* v_reuseFailAlloc_6450_; 
v_reuseFailAlloc_6450_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6450_, 0, v_a_6441_);
lean_ctor_set(v_reuseFailAlloc_6450_, 1, v_trace_6434_);
lean_ctor_set(v_reuseFailAlloc_6450_, 2, v_buildTime_6435_);
lean_ctor_set_uint8(v_reuseFailAlloc_6450_, sizeof(void*)*3, v_action_6432_);
lean_ctor_set_uint8(v_reuseFailAlloc_6450_, sizeof(void*)*3 + 1, v_wantsRebuild_6433_);
v___x_6446_ = v_reuseFailAlloc_6450_;
goto v_reusejp_6445_;
}
v_reusejp_6445_:
{
lean_object* v___x_6448_; 
if (v_isShared_6444_ == 0)
{
lean_ctor_set(v___x_6443_, 1, v___x_6446_);
v___x_6448_ = v___x_6443_;
goto v_reusejp_6447_;
}
else
{
lean_object* v_reuseFailAlloc_6449_; 
v_reuseFailAlloc_6449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_a_6440_);
lean_ctor_set(v_reuseFailAlloc_6449_, 1, v___x_6446_);
v___x_6448_ = v_reuseFailAlloc_6449_;
goto v_reusejp_6447_;
}
v_reusejp_6447_:
{
return v___x_6448_;
}
}
}
}
else
{
lean_object* v_a_6452_; lean_object* v_a_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6463_; 
v_a_6452_ = lean_ctor_get(v___x_6439_, 0);
v_a_6453_ = lean_ctor_get(v___x_6439_, 1);
v_isSharedCheck_6463_ = !lean_is_exclusive(v___x_6439_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6455_ = v___x_6439_;
v_isShared_6456_ = v_isSharedCheck_6463_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_a_6453_);
lean_inc(v_a_6452_);
lean_dec(v___x_6439_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6463_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6458_; 
if (v_isShared_6438_ == 0)
{
lean_ctor_set(v___x_6437_, 0, v_a_6453_);
v___x_6458_ = v___x_6437_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v_a_6453_);
lean_ctor_set(v_reuseFailAlloc_6462_, 1, v_trace_6434_);
lean_ctor_set(v_reuseFailAlloc_6462_, 2, v_buildTime_6435_);
lean_ctor_set_uint8(v_reuseFailAlloc_6462_, sizeof(void*)*3, v_action_6432_);
lean_ctor_set_uint8(v_reuseFailAlloc_6462_, sizeof(void*)*3 + 1, v_wantsRebuild_6433_);
v___x_6458_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
lean_object* v___x_6460_; 
if (v_isShared_6456_ == 0)
{
lean_ctor_set(v___x_6455_, 1, v___x_6458_);
v___x_6460_ = v___x_6455_;
goto v_reusejp_6459_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6452_);
lean_ctor_set(v_reuseFailAlloc_6461_, 1, v___x_6458_);
v___x_6460_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6459_;
}
v_reusejp_6459_:
{
return v___x_6460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6465_, lean_object* v_srcFile_6466_, lean_object* v___x_6467_, lean_object* v_compiler_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_){
_start:
{
lean_object* v_res_6476_; 
v_res_6476_ = l_Lake_buildO___lam__1(v_oFile_6465_, v_srcFile_6466_, v___x_6467_, v_compiler_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_);
lean_dec_ref(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec(v___y_6471_);
lean_dec(v___y_6470_);
lean_dec_ref(v___y_6469_);
lean_dec_ref(v___x_6467_);
return v_res_6476_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6480_; lean_object* v___x_6481_; 
v___x_6480_ = l_Lake_Hash_nil;
v___x_6481_ = lean_box_uint64(v___x_6480_);
return v___x_6481_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6482_, lean_object* v___f_6483_, lean_object* v_extraDepTrace_6484_, lean_object* v_weakArgs_6485_, lean_object* v_oFile_6486_, lean_object* v_compiler_6487_, lean_object* v___x_6488_, lean_object* v___f_6489_, lean_object* v_srcFile_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_){
_start:
{
lean_object* v_log_6498_; uint8_t v_action_6499_; uint8_t v_wantsRebuild_6500_; lean_object* v_trace_6501_; lean_object* v_buildTime_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6587_; 
v_log_6498_ = lean_ctor_get(v___y_6496_, 0);
v_action_6499_ = lean_ctor_get_uint8(v___y_6496_, sizeof(void*)*3);
v_wantsRebuild_6500_ = lean_ctor_get_uint8(v___y_6496_, sizeof(void*)*3 + 1);
v_trace_6501_ = lean_ctor_get(v___y_6496_, 1);
v_buildTime_6502_ = lean_ctor_get(v___y_6496_, 2);
v_isSharedCheck_6587_ = !lean_is_exclusive(v___y_6496_);
if (v_isSharedCheck_6587_ == 0)
{
v___x_6504_ = v___y_6496_;
v_isShared_6505_ = v_isSharedCheck_6587_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_buildTime_6502_);
lean_inc(v_trace_6501_);
lean_inc(v_log_6498_);
lean_dec(v___y_6496_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6587_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v___x_6506_; lean_object* v___x_6507_; uint64_t v___y_6509_; uint64_t v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; uint8_t v___x_6575_; 
v___x_6506_ = l_Lake_platformTrace;
v___x_6507_ = l_Lake_BuildTrace_mix(v_trace_6501_, v___x_6506_);
v___x_6572_ = l_Lake_Hash_nil;
v___x_6573_ = lean_unsigned_to_nat(0u);
v___x_6574_ = lean_array_get_size(v_traceArgs_6482_);
v___x_6575_ = lean_nat_dec_lt(v___x_6573_, v___x_6574_);
if (v___x_6575_ == 0)
{
lean_dec_ref(v___f_6489_);
lean_dec_ref(v___x_6488_);
v___y_6509_ = v___x_6572_;
goto v___jp_6508_;
}
else
{
uint8_t v___x_6576_; 
v___x_6576_ = lean_nat_dec_le(v___x_6574_, v___x_6574_);
if (v___x_6576_ == 0)
{
if (v___x_6575_ == 0)
{
lean_dec_ref(v___f_6489_);
lean_dec_ref(v___x_6488_);
v___y_6509_ = v___x_6572_;
goto v___jp_6508_;
}
else
{
size_t v___x_6577_; size_t v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; uint64_t v___x_6581_; 
v___x_6577_ = ((size_t)0ULL);
v___x_6578_ = lean_usize_of_nat(v___x_6574_);
v___x_6579_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6482_);
v___x_6580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6488_, v___f_6489_, v_traceArgs_6482_, v___x_6577_, v___x_6578_, v___x_6579_);
v___x_6581_ = lean_unbox_uint64(v___x_6580_);
lean_dec(v___x_6580_);
v___y_6509_ = v___x_6581_;
goto v___jp_6508_;
}
}
else
{
size_t v___x_6582_; size_t v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; uint64_t v___x_6586_; 
v___x_6582_ = ((size_t)0ULL);
v___x_6583_ = lean_usize_of_nat(v___x_6574_);
v___x_6584_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6482_);
v___x_6585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6488_, v___f_6489_, v_traceArgs_6482_, v___x_6582_, v___x_6583_, v___x_6584_);
v___x_6586_ = lean_unbox_uint64(v___x_6585_);
lean_dec(v___x_6585_);
v___y_6509_ = v___x_6586_;
goto v___jp_6508_;
}
}
v___jp_6508_:
{
lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6521_; 
v___x_6510_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6511_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6482_);
v___x_6512_ = lean_array_to_list(v_traceArgs_6482_);
v___x_6513_ = l_List_toString___redArg(v___f_6483_, v___x_6512_);
v___x_6514_ = lean_string_append(v___x_6511_, v___x_6513_);
lean_dec_ref(v___x_6513_);
v___x_6515_ = lean_string_append(v___x_6510_, v___x_6514_);
lean_dec_ref(v___x_6514_);
v___x_6516_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6517_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6518_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6518_, 0, v___x_6515_);
lean_ctor_set(v___x_6518_, 1, v___x_6516_);
lean_ctor_set(v___x_6518_, 2, v___x_6517_);
lean_ctor_set_uint64(v___x_6518_, sizeof(void*)*3, v___y_6509_);
v___x_6519_ = l_Lake_BuildTrace_mix(v___x_6507_, v___x_6518_);
if (v_isShared_6505_ == 0)
{
lean_ctor_set(v___x_6504_, 1, v___x_6519_);
v___x_6521_ = v___x_6504_;
goto v_reusejp_6520_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_log_6498_);
lean_ctor_set(v_reuseFailAlloc_6571_, 1, v___x_6519_);
lean_ctor_set(v_reuseFailAlloc_6571_, 2, v_buildTime_6502_);
lean_ctor_set_uint8(v_reuseFailAlloc_6571_, sizeof(void*)*3, v_action_6499_);
lean_ctor_set_uint8(v_reuseFailAlloc_6571_, sizeof(void*)*3 + 1, v_wantsRebuild_6500_);
v___x_6521_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6520_;
}
v_reusejp_6520_:
{
lean_object* v___x_6522_; 
lean_inc_ref(v___y_6495_);
lean_inc(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc(v___y_6492_);
lean_inc_ref(v___y_6491_);
v___x_6522_ = lean_apply_7(v_extraDepTrace_6484_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___x_6521_, lean_box(0));
if (lean_obj_tag(v___x_6522_) == 0)
{
lean_object* v_a_6523_; lean_object* v_a_6524_; lean_object* v_log_6525_; uint8_t v_action_6526_; uint8_t v_wantsRebuild_6527_; lean_object* v_trace_6528_; lean_object* v_buildTime_6529_; lean_object* v___x_6531_; uint8_t v_isShared_6532_; uint8_t v_isSharedCheck_6561_; 
v_a_6523_ = lean_ctor_get(v___x_6522_, 1);
lean_inc(v_a_6523_);
v_a_6524_ = lean_ctor_get(v___x_6522_, 0);
lean_inc(v_a_6524_);
lean_dec_ref_known(v___x_6522_, 2);
v_log_6525_ = lean_ctor_get(v_a_6523_, 0);
v_action_6526_ = lean_ctor_get_uint8(v_a_6523_, sizeof(void*)*3);
v_wantsRebuild_6527_ = lean_ctor_get_uint8(v_a_6523_, sizeof(void*)*3 + 1);
v_trace_6528_ = lean_ctor_get(v_a_6523_, 1);
v_buildTime_6529_ = lean_ctor_get(v_a_6523_, 2);
v_isSharedCheck_6561_ = !lean_is_exclusive(v_a_6523_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6531_ = v_a_6523_;
v_isShared_6532_ = v_isSharedCheck_6561_;
goto v_resetjp_6530_;
}
else
{
lean_inc(v_buildTime_6529_);
lean_inc(v_trace_6528_);
lean_inc(v_log_6525_);
lean_dec(v_a_6523_);
v___x_6531_ = lean_box(0);
v_isShared_6532_ = v_isSharedCheck_6561_;
goto v_resetjp_6530_;
}
v_resetjp_6530_:
{
lean_object* v___x_6533_; lean_object* v___x_6535_; 
v___x_6533_ = l_Lake_BuildTrace_mix(v_trace_6528_, v_a_6524_);
if (v_isShared_6532_ == 0)
{
lean_ctor_set(v___x_6531_, 1, v___x_6533_);
v___x_6535_ = v___x_6531_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_log_6525_);
lean_ctor_set(v_reuseFailAlloc_6560_, 1, v___x_6533_);
lean_ctor_set(v_reuseFailAlloc_6560_, 2, v_buildTime_6529_);
lean_ctor_set_uint8(v_reuseFailAlloc_6560_, sizeof(void*)*3, v_action_6526_);
lean_ctor_set_uint8(v_reuseFailAlloc_6560_, sizeof(void*)*3 + 1, v_wantsRebuild_6527_);
v___x_6535_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
lean_object* v___x_6536_; lean_object* v___f_6537_; uint8_t v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; 
v___x_6536_ = l_Array_append___redArg(v_weakArgs_6485_, v_traceArgs_6482_);
lean_dec_ref(v_traceArgs_6482_);
lean_inc_ref(v_oFile_6486_);
v___f_6537_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6537_, 0, v_oFile_6486_);
lean_closure_set(v___f_6537_, 1, v_srcFile_6490_);
lean_closure_set(v___f_6537_, 2, v___x_6536_);
lean_closure_set(v___f_6537_, 3, v_compiler_6487_);
v___x_6538_ = 0;
v___x_6539_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6540_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6486_, v___f_6537_, v___x_6538_, v___x_6539_, v___x_6538_, v___x_6538_, v___x_6538_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___x_6535_);
if (lean_obj_tag(v___x_6540_) == 0)
{
lean_object* v_a_6541_; lean_object* v_a_6542_; lean_object* v___x_6544_; uint8_t v_isShared_6545_; uint8_t v_isSharedCheck_6550_; 
v_a_6541_ = lean_ctor_get(v___x_6540_, 0);
v_a_6542_ = lean_ctor_get(v___x_6540_, 1);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6544_ = v___x_6540_;
v_isShared_6545_ = v_isSharedCheck_6550_;
goto v_resetjp_6543_;
}
else
{
lean_inc(v_a_6542_);
lean_inc(v_a_6541_);
lean_dec(v___x_6540_);
v___x_6544_ = lean_box(0);
v_isShared_6545_ = v_isSharedCheck_6550_;
goto v_resetjp_6543_;
}
v_resetjp_6543_:
{
lean_object* v_path_6546_; lean_object* v___x_6548_; 
v_path_6546_ = lean_ctor_get(v_a_6541_, 1);
lean_inc_ref(v_path_6546_);
lean_dec(v_a_6541_);
if (v_isShared_6545_ == 0)
{
lean_ctor_set(v___x_6544_, 0, v_path_6546_);
v___x_6548_ = v___x_6544_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_path_6546_);
lean_ctor_set(v_reuseFailAlloc_6549_, 1, v_a_6542_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
else
{
lean_object* v_a_6551_; lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6559_; 
v_a_6551_ = lean_ctor_get(v___x_6540_, 0);
v_a_6552_ = lean_ctor_get(v___x_6540_, 1);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6554_ = v___x_6540_;
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_inc(v_a_6551_);
lean_dec(v___x_6540_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6557_; 
if (v_isShared_6555_ == 0)
{
v___x_6557_ = v___x_6554_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6551_);
lean_ctor_set(v_reuseFailAlloc_6558_, 1, v_a_6552_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
return v___x_6557_;
}
}
}
}
}
}
else
{
lean_object* v_a_6562_; lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6570_; 
lean_dec_ref(v___y_6491_);
lean_dec_ref(v_srcFile_6490_);
lean_dec_ref(v_compiler_6487_);
lean_dec_ref(v_oFile_6486_);
lean_dec_ref(v_weakArgs_6485_);
lean_dec_ref(v_traceArgs_6482_);
v_a_6562_ = lean_ctor_get(v___x_6522_, 0);
v_a_6563_ = lean_ctor_get(v___x_6522_, 1);
v_isSharedCheck_6570_ = !lean_is_exclusive(v___x_6522_);
if (v_isSharedCheck_6570_ == 0)
{
v___x_6565_ = v___x_6522_;
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_inc(v_a_6562_);
lean_dec(v___x_6522_);
v___x_6565_ = lean_box(0);
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
v_resetjp_6564_:
{
lean_object* v___x_6568_; 
if (v_isShared_6566_ == 0)
{
v___x_6568_ = v___x_6565_;
goto v_reusejp_6567_;
}
else
{
lean_object* v_reuseFailAlloc_6569_; 
v_reuseFailAlloc_6569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_a_6562_);
lean_ctor_set(v_reuseFailAlloc_6569_, 1, v_a_6563_);
v___x_6568_ = v_reuseFailAlloc_6569_;
goto v_reusejp_6567_;
}
v_reusejp_6567_:
{
return v___x_6568_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6588_, lean_object* v___f_6589_, lean_object* v_extraDepTrace_6590_, lean_object* v_weakArgs_6591_, lean_object* v_oFile_6592_, lean_object* v_compiler_6593_, lean_object* v___x_6594_, lean_object* v___f_6595_, lean_object* v_srcFile_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Lake_buildO___lam__2(v_traceArgs_6588_, v___f_6589_, v_extraDepTrace_6590_, v_weakArgs_6591_, v_oFile_6592_, v_compiler_6593_, v___x_6594_, v___f_6595_, v_srcFile_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_);
lean_dec_ref(v___y_6601_);
lean_dec(v___y_6600_);
lean_dec(v___y_6599_);
lean_dec(v___y_6598_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6607_, lean_object* v_srcJob_6608_, lean_object* v_weakArgs_6609_, lean_object* v_traceArgs_6610_, lean_object* v_compiler_6611_, lean_object* v_extraDepTrace_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_){
_start:
{
lean_object* v___f_6620_; lean_object* v___x_6621_; lean_object* v___f_6622_; lean_object* v___x_6623_; lean_object* v___f_6624_; lean_object* v___x_6625_; uint8_t v___x_6626_; lean_object* v___x_6627_; 
v___f_6620_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6621_ = l_Lake_instDataKindFilePath;
v___f_6622_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6623_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6624_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6624_, 0, v_traceArgs_6610_);
lean_closure_set(v___f_6624_, 1, v___f_6622_);
lean_closure_set(v___f_6624_, 2, v_extraDepTrace_6612_);
lean_closure_set(v___f_6624_, 3, v_weakArgs_6609_);
lean_closure_set(v___f_6624_, 4, v_oFile_6607_);
lean_closure_set(v___f_6624_, 5, v_compiler_6611_);
lean_closure_set(v___f_6624_, 6, v___x_6623_);
lean_closure_set(v___f_6624_, 7, v___f_6620_);
v___x_6625_ = lean_unsigned_to_nat(0u);
v___x_6626_ = 0;
v___x_6627_ = l_Lake_Job_mapM___redArg(v___x_6621_, v_srcJob_6608_, v___f_6624_, v___x_6625_, v___x_6626_, v_a_6613_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_);
return v___x_6627_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6628_, lean_object* v_srcJob_6629_, lean_object* v_weakArgs_6630_, lean_object* v_traceArgs_6631_, lean_object* v_compiler_6632_, lean_object* v_extraDepTrace_6633_, lean_object* v_a_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_){
_start:
{
lean_object* v_res_6641_; 
v_res_6641_ = l_Lake_buildO(v_oFile_6628_, v_srcJob_6629_, v_weakArgs_6630_, v_traceArgs_6631_, v_compiler_6632_, v_extraDepTrace_6633_, v_a_6634_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_);
lean_dec_ref(v_a_6639_);
lean_dec_ref(v_a_6638_);
lean_dec(v_a_6637_);
lean_dec(v_a_6636_);
lean_dec(v_a_6635_);
return v_res_6641_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; 
v___x_6643_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6644_ = lean_unsigned_to_nat(2u);
v___x_6645_ = lean_mk_empty_array_with_capacity(v___x_6644_);
v___x_6646_ = lean_array_push(v___x_6645_, v___x_6643_);
return v___x_6646_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6647_, lean_object* v_traceArgs_6648_, lean_object* v_oFile_6649_, lean_object* v_srcFile_6650_, lean_object* v_leanIncludeDir_x3f_6651_, lean_object* v___y_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_){
_start:
{
lean_object* v_toContext_6659_; lean_object* v_lakeEnv_6660_; lean_object* v_log_6661_; uint8_t v_action_6662_; uint8_t v_wantsRebuild_6663_; lean_object* v_trace_6664_; lean_object* v_buildTime_6665_; lean_object* v___x_6667_; uint8_t v_isShared_6668_; uint8_t v_isSharedCheck_6706_; 
v_toContext_6659_ = lean_ctor_get(v___y_6656_, 1);
v_lakeEnv_6660_ = lean_ctor_get(v_toContext_6659_, 0);
v_log_6661_ = lean_ctor_get(v___y_6657_, 0);
v_action_6662_ = lean_ctor_get_uint8(v___y_6657_, sizeof(void*)*3);
v_wantsRebuild_6663_ = lean_ctor_get_uint8(v___y_6657_, sizeof(void*)*3 + 1);
v_trace_6664_ = lean_ctor_get(v___y_6657_, 1);
v_buildTime_6665_ = lean_ctor_get(v___y_6657_, 2);
v_isSharedCheck_6706_ = !lean_is_exclusive(v___y_6657_);
if (v_isSharedCheck_6706_ == 0)
{
v___x_6667_ = v___y_6657_;
v_isShared_6668_ = v_isSharedCheck_6706_;
goto v_resetjp_6666_;
}
else
{
lean_inc(v_buildTime_6665_);
lean_inc(v_trace_6664_);
lean_inc(v_log_6661_);
lean_dec(v___y_6657_);
v___x_6667_ = lean_box(0);
v_isShared_6668_ = v_isSharedCheck_6706_;
goto v_resetjp_6666_;
}
v_resetjp_6666_:
{
lean_object* v_lean_6669_; lean_object* v___y_6671_; 
v_lean_6669_ = lean_ctor_get(v_lakeEnv_6660_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6651_) == 0)
{
lean_object* v_includeDir_6704_; 
v_includeDir_6704_ = lean_ctor_get(v_lean_6669_, 4);
lean_inc_ref(v_includeDir_6704_);
v___y_6671_ = v_includeDir_6704_;
goto v___jp_6670_;
}
else
{
lean_object* v_val_6705_; 
v_val_6705_ = lean_ctor_get(v_leanIncludeDir_x3f_6651_, 0);
lean_inc(v_val_6705_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6651_, 1);
v___y_6671_ = v_val_6705_;
goto v___jp_6670_;
}
v___jp_6670_:
{
lean_object* v_cc_6672_; lean_object* v_ccFlags_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; 
v_cc_6672_ = lean_ctor_get(v_lean_6669_, 14);
v_ccFlags_6673_ = lean_ctor_get(v_lean_6669_, 18);
v___x_6674_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6675_ = lean_array_push(v___x_6674_, v___y_6671_);
v___x_6676_ = l_Array_append___redArg(v___x_6675_, v_ccFlags_6673_);
v___x_6677_ = l_Array_append___redArg(v___x_6676_, v_weakArgs_6647_);
v___x_6678_ = l_Array_append___redArg(v___x_6677_, v_traceArgs_6648_);
lean_inc_ref(v_cc_6672_);
v___x_6679_ = l_Lake_compileO(v_oFile_6649_, v_srcFile_6650_, v___x_6678_, v_cc_6672_, v_log_6661_);
lean_dec_ref(v___x_6678_);
if (lean_obj_tag(v___x_6679_) == 0)
{
lean_object* v_a_6680_; lean_object* v_a_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6691_; 
v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
v_a_6681_ = lean_ctor_get(v___x_6679_, 1);
v_isSharedCheck_6691_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6691_ == 0)
{
v___x_6683_ = v___x_6679_;
v_isShared_6684_ = v_isSharedCheck_6691_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_a_6681_);
lean_inc(v_a_6680_);
lean_dec(v___x_6679_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6691_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v___x_6686_; 
if (v_isShared_6668_ == 0)
{
lean_ctor_set(v___x_6667_, 0, v_a_6681_);
v___x_6686_ = v___x_6667_;
goto v_reusejp_6685_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v_a_6681_);
lean_ctor_set(v_reuseFailAlloc_6690_, 1, v_trace_6664_);
lean_ctor_set(v_reuseFailAlloc_6690_, 2, v_buildTime_6665_);
lean_ctor_set_uint8(v_reuseFailAlloc_6690_, sizeof(void*)*3, v_action_6662_);
lean_ctor_set_uint8(v_reuseFailAlloc_6690_, sizeof(void*)*3 + 1, v_wantsRebuild_6663_);
v___x_6686_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6685_;
}
v_reusejp_6685_:
{
lean_object* v___x_6688_; 
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 1, v___x_6686_);
v___x_6688_ = v___x_6683_;
goto v_reusejp_6687_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v_a_6680_);
lean_ctor_set(v_reuseFailAlloc_6689_, 1, v___x_6686_);
v___x_6688_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6687_;
}
v_reusejp_6687_:
{
return v___x_6688_;
}
}
}
}
else
{
lean_object* v_a_6692_; lean_object* v_a_6693_; lean_object* v___x_6695_; uint8_t v_isShared_6696_; uint8_t v_isSharedCheck_6703_; 
v_a_6692_ = lean_ctor_get(v___x_6679_, 0);
v_a_6693_ = lean_ctor_get(v___x_6679_, 1);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6695_ = v___x_6679_;
v_isShared_6696_ = v_isSharedCheck_6703_;
goto v_resetjp_6694_;
}
else
{
lean_inc(v_a_6693_);
lean_inc(v_a_6692_);
lean_dec(v___x_6679_);
v___x_6695_ = lean_box(0);
v_isShared_6696_ = v_isSharedCheck_6703_;
goto v_resetjp_6694_;
}
v_resetjp_6694_:
{
lean_object* v___x_6698_; 
if (v_isShared_6668_ == 0)
{
lean_ctor_set(v___x_6667_, 0, v_a_6693_);
v___x_6698_ = v___x_6667_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6693_);
lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_trace_6664_);
lean_ctor_set(v_reuseFailAlloc_6702_, 2, v_buildTime_6665_);
lean_ctor_set_uint8(v_reuseFailAlloc_6702_, sizeof(void*)*3, v_action_6662_);
lean_ctor_set_uint8(v_reuseFailAlloc_6702_, sizeof(void*)*3 + 1, v_wantsRebuild_6663_);
v___x_6698_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
lean_object* v___x_6700_; 
if (v_isShared_6696_ == 0)
{
lean_ctor_set(v___x_6695_, 1, v___x_6698_);
v___x_6700_ = v___x_6695_;
goto v_reusejp_6699_;
}
else
{
lean_object* v_reuseFailAlloc_6701_; 
v_reuseFailAlloc_6701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_a_6692_);
lean_ctor_set(v_reuseFailAlloc_6701_, 1, v___x_6698_);
v___x_6700_ = v_reuseFailAlloc_6701_;
goto v_reusejp_6699_;
}
v_reusejp_6699_:
{
return v___x_6700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6707_, lean_object* v_traceArgs_6708_, lean_object* v_oFile_6709_, lean_object* v_srcFile_6710_, lean_object* v_leanIncludeDir_x3f_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_){
_start:
{
lean_object* v_res_6719_; 
v_res_6719_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6707_, v_traceArgs_6708_, v_oFile_6709_, v_srcFile_6710_, v_leanIncludeDir_x3f_6711_, v___y_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_);
lean_dec_ref(v___y_6716_);
lean_dec(v___y_6715_);
lean_dec(v___y_6714_);
lean_dec(v___y_6713_);
lean_dec_ref(v___y_6712_);
lean_dec_ref(v_traceArgs_6708_);
lean_dec_ref(v_weakArgs_6707_);
return v_res_6719_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6720_, size_t v_i_6721_, size_t v_stop_6722_, uint64_t v_b_6723_){
_start:
{
uint8_t v___x_6724_; 
v___x_6724_ = lean_usize_dec_eq(v_i_6721_, v_stop_6722_);
if (v___x_6724_ == 0)
{
lean_object* v___x_6725_; uint64_t v___x_6726_; uint64_t v___x_6727_; uint64_t v___x_6728_; uint64_t v___x_6729_; size_t v___x_6730_; size_t v___x_6731_; 
v___x_6725_ = lean_array_uget_borrowed(v_as_6720_, v_i_6721_);
v___x_6726_ = l_Lake_Hash_nil;
v___x_6727_ = lean_string_hash(v___x_6725_);
v___x_6728_ = lean_uint64_mix_hash(v___x_6726_, v___x_6727_);
v___x_6729_ = lean_uint64_mix_hash(v_b_6723_, v___x_6728_);
v___x_6730_ = ((size_t)1ULL);
v___x_6731_ = lean_usize_add(v_i_6721_, v___x_6730_);
v_i_6721_ = v___x_6731_;
v_b_6723_ = v___x_6729_;
goto _start;
}
else
{
return v_b_6723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6733_, lean_object* v_i_6734_, lean_object* v_stop_6735_, lean_object* v_b_6736_){
_start:
{
size_t v_i_boxed_6737_; size_t v_stop_boxed_6738_; uint64_t v_b_boxed_6739_; uint64_t v_res_6740_; lean_object* v_r_6741_; 
v_i_boxed_6737_ = lean_unbox_usize(v_i_6734_);
lean_dec(v_i_6734_);
v_stop_boxed_6738_ = lean_unbox_usize(v_stop_6735_);
lean_dec(v_stop_6735_);
v_b_boxed_6739_ = lean_unbox_uint64(v_b_6736_);
lean_dec_ref(v_b_6736_);
v_res_6740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6733_, v_i_boxed_6737_, v_stop_boxed_6738_, v_b_boxed_6739_);
lean_dec_ref(v_as_6733_);
v_r_6741_ = lean_box_uint64(v_res_6740_);
return v_r_6741_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6743_, lean_object* v_x_6744_){
_start:
{
if (lean_obj_tag(v_x_6744_) == 0)
{
return v_x_6743_;
}
else
{
lean_object* v_head_6745_; lean_object* v_tail_6746_; lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; 
v_head_6745_ = lean_ctor_get(v_x_6744_, 0);
v_tail_6746_ = lean_ctor_get(v_x_6744_, 1);
v___x_6747_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6748_ = lean_string_append(v_x_6743_, v___x_6747_);
v___x_6749_ = lean_string_append(v___x_6748_, v_head_6745_);
v_x_6743_ = v___x_6749_;
v_x_6744_ = v_tail_6746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6751_, lean_object* v_x_6752_){
_start:
{
lean_object* v_res_6753_; 
v_res_6753_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6751_, v_x_6752_);
lean_dec(v_x_6752_);
return v_res_6753_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6757_){
_start:
{
if (lean_obj_tag(v_x_6757_) == 0)
{
lean_object* v___x_6758_; 
v___x_6758_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6758_;
}
else
{
lean_object* v_tail_6759_; 
v_tail_6759_ = lean_ctor_get(v_x_6757_, 1);
if (lean_obj_tag(v_tail_6759_) == 0)
{
lean_object* v_head_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; 
v_head_6760_ = lean_ctor_get(v_x_6757_, 0);
v___x_6761_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6762_ = lean_string_append(v___x_6761_, v_head_6760_);
v___x_6763_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6764_ = lean_string_append(v___x_6762_, v___x_6763_);
return v___x_6764_;
}
else
{
lean_object* v_head_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; uint32_t v___x_6769_; lean_object* v___x_6770_; 
v_head_6765_ = lean_ctor_get(v_x_6757_, 0);
v___x_6766_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6767_ = lean_string_append(v___x_6766_, v_head_6765_);
v___x_6768_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6767_, v_tail_6759_);
v___x_6769_ = 93;
v___x_6770_ = lean_string_push(v___x_6768_, v___x_6769_);
return v___x_6770_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6771_);
lean_dec(v_x_6771_);
return v_res_6772_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6773_, lean_object* v_traceArgs_6774_, lean_object* v_oFile_6775_, lean_object* v_leanIncludeDir_x3f_6776_, lean_object* v_srcFile_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_){
_start:
{
lean_object* v_log_6785_; uint8_t v_action_6786_; uint8_t v_wantsRebuild_6787_; lean_object* v_trace_6788_; lean_object* v_buildTime_6789_; lean_object* v___x_6791_; uint8_t v_isShared_6792_; uint8_t v_isSharedCheck_6846_; 
v_log_6785_ = lean_ctor_get(v___y_6783_, 0);
v_action_6786_ = lean_ctor_get_uint8(v___y_6783_, sizeof(void*)*3);
v_wantsRebuild_6787_ = lean_ctor_get_uint8(v___y_6783_, sizeof(void*)*3 + 1);
v_trace_6788_ = lean_ctor_get(v___y_6783_, 1);
v_buildTime_6789_ = lean_ctor_get(v___y_6783_, 2);
v_isSharedCheck_6846_ = !lean_is_exclusive(v___y_6783_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6791_ = v___y_6783_;
v_isShared_6792_ = v_isSharedCheck_6846_;
goto v_resetjp_6790_;
}
else
{
lean_inc(v_buildTime_6789_);
lean_inc(v_trace_6788_);
lean_inc(v_log_6785_);
lean_dec(v___y_6783_);
v___x_6791_ = lean_box(0);
v_isShared_6792_ = v_isSharedCheck_6846_;
goto v_resetjp_6790_;
}
v_resetjp_6790_:
{
lean_object* v_leanTrace_6793_; lean_object* v___f_6794_; lean_object* v___x_6795_; uint64_t v___y_6797_; uint64_t v___x_6835_; lean_object* v___x_6836_; lean_object* v___x_6837_; uint8_t v___x_6838_; 
v_leanTrace_6793_ = lean_ctor_get(v___y_6782_, 2);
lean_inc_ref(v_oFile_6775_);
lean_inc_ref(v_traceArgs_6774_);
v___f_6794_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6794_, 0, v_weakArgs_6773_);
lean_closure_set(v___f_6794_, 1, v_traceArgs_6774_);
lean_closure_set(v___f_6794_, 2, v_oFile_6775_);
lean_closure_set(v___f_6794_, 3, v_srcFile_6777_);
lean_closure_set(v___f_6794_, 4, v_leanIncludeDir_x3f_6776_);
lean_inc_ref(v_leanTrace_6793_);
v___x_6795_ = l_Lake_BuildTrace_mix(v_trace_6788_, v_leanTrace_6793_);
v___x_6835_ = l_Lake_Hash_nil;
v___x_6836_ = lean_unsigned_to_nat(0u);
v___x_6837_ = lean_array_get_size(v_traceArgs_6774_);
v___x_6838_ = lean_nat_dec_lt(v___x_6836_, v___x_6837_);
if (v___x_6838_ == 0)
{
v___y_6797_ = v___x_6835_;
goto v___jp_6796_;
}
else
{
uint8_t v___x_6839_; 
v___x_6839_ = lean_nat_dec_le(v___x_6837_, v___x_6837_);
if (v___x_6839_ == 0)
{
if (v___x_6838_ == 0)
{
v___y_6797_ = v___x_6835_;
goto v___jp_6796_;
}
else
{
size_t v___x_6840_; size_t v___x_6841_; uint64_t v___x_6842_; 
v___x_6840_ = ((size_t)0ULL);
v___x_6841_ = lean_usize_of_nat(v___x_6837_);
v___x_6842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6774_, v___x_6840_, v___x_6841_, v___x_6835_);
v___y_6797_ = v___x_6842_;
goto v___jp_6796_;
}
}
else
{
size_t v___x_6843_; size_t v___x_6844_; uint64_t v___x_6845_; 
v___x_6843_ = ((size_t)0ULL);
v___x_6844_ = lean_usize_of_nat(v___x_6837_);
v___x_6845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6774_, v___x_6843_, v___x_6844_, v___x_6835_);
v___y_6797_ = v___x_6845_;
goto v___jp_6796_;
}
}
v___jp_6796_:
{
lean_object* v___x_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6811_; 
v___x_6798_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6799_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6800_ = lean_array_to_list(v_traceArgs_6774_);
v___x_6801_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6800_);
lean_dec(v___x_6800_);
v___x_6802_ = lean_string_append(v___x_6799_, v___x_6801_);
lean_dec_ref(v___x_6801_);
v___x_6803_ = lean_string_append(v___x_6798_, v___x_6802_);
lean_dec_ref(v___x_6802_);
v___x_6804_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6805_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6806_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6806_, 0, v___x_6803_);
lean_ctor_set(v___x_6806_, 1, v___x_6804_);
lean_ctor_set(v___x_6806_, 2, v___x_6805_);
lean_ctor_set_uint64(v___x_6806_, sizeof(void*)*3, v___y_6797_);
v___x_6807_ = l_Lake_BuildTrace_mix(v___x_6795_, v___x_6806_);
v___x_6808_ = l_Lake_platformTrace;
v___x_6809_ = l_Lake_BuildTrace_mix(v___x_6807_, v___x_6808_);
if (v_isShared_6792_ == 0)
{
lean_ctor_set(v___x_6791_, 1, v___x_6809_);
v___x_6811_ = v___x_6791_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v_log_6785_);
lean_ctor_set(v_reuseFailAlloc_6834_, 1, v___x_6809_);
lean_ctor_set(v_reuseFailAlloc_6834_, 2, v_buildTime_6789_);
lean_ctor_set_uint8(v_reuseFailAlloc_6834_, sizeof(void*)*3, v_action_6786_);
lean_ctor_set_uint8(v_reuseFailAlloc_6834_, sizeof(void*)*3 + 1, v_wantsRebuild_6787_);
v___x_6811_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
uint8_t v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; 
v___x_6812_ = 0;
v___x_6813_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6814_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6775_, v___f_6794_, v___x_6812_, v___x_6813_, v___x_6812_, v___x_6812_, v___x_6812_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___x_6811_);
if (lean_obj_tag(v___x_6814_) == 0)
{
lean_object* v_a_6815_; lean_object* v_a_6816_; lean_object* v___x_6818_; uint8_t v_isShared_6819_; uint8_t v_isSharedCheck_6824_; 
v_a_6815_ = lean_ctor_get(v___x_6814_, 0);
v_a_6816_ = lean_ctor_get(v___x_6814_, 1);
v_isSharedCheck_6824_ = !lean_is_exclusive(v___x_6814_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6818_ = v___x_6814_;
v_isShared_6819_ = v_isSharedCheck_6824_;
goto v_resetjp_6817_;
}
else
{
lean_inc(v_a_6816_);
lean_inc(v_a_6815_);
lean_dec(v___x_6814_);
v___x_6818_ = lean_box(0);
v_isShared_6819_ = v_isSharedCheck_6824_;
goto v_resetjp_6817_;
}
v_resetjp_6817_:
{
lean_object* v_path_6820_; lean_object* v___x_6822_; 
v_path_6820_ = lean_ctor_get(v_a_6815_, 1);
lean_inc_ref(v_path_6820_);
lean_dec(v_a_6815_);
if (v_isShared_6819_ == 0)
{
lean_ctor_set(v___x_6818_, 0, v_path_6820_);
v___x_6822_ = v___x_6818_;
goto v_reusejp_6821_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_path_6820_);
lean_ctor_set(v_reuseFailAlloc_6823_, 1, v_a_6816_);
v___x_6822_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6821_;
}
v_reusejp_6821_:
{
return v___x_6822_;
}
}
}
else
{
lean_object* v_a_6825_; lean_object* v_a_6826_; lean_object* v___x_6828_; uint8_t v_isShared_6829_; uint8_t v_isSharedCheck_6833_; 
v_a_6825_ = lean_ctor_get(v___x_6814_, 0);
v_a_6826_ = lean_ctor_get(v___x_6814_, 1);
v_isSharedCheck_6833_ = !lean_is_exclusive(v___x_6814_);
if (v_isSharedCheck_6833_ == 0)
{
v___x_6828_ = v___x_6814_;
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
else
{
lean_inc(v_a_6826_);
lean_inc(v_a_6825_);
lean_dec(v___x_6814_);
v___x_6828_ = lean_box(0);
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
v_resetjp_6827_:
{
lean_object* v___x_6831_; 
if (v_isShared_6829_ == 0)
{
v___x_6831_ = v___x_6828_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6825_);
lean_ctor_set(v_reuseFailAlloc_6832_, 1, v_a_6826_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
return v___x_6831_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6847_, lean_object* v_traceArgs_6848_, lean_object* v_oFile_6849_, lean_object* v_leanIncludeDir_x3f_6850_, lean_object* v_srcFile_6851_, lean_object* v___y_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_){
_start:
{
lean_object* v_res_6859_; 
v_res_6859_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6847_, v_traceArgs_6848_, v_oFile_6849_, v_leanIncludeDir_x3f_6850_, v_srcFile_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_);
lean_dec_ref(v___y_6856_);
lean_dec(v___y_6855_);
lean_dec(v___y_6854_);
lean_dec(v___y_6853_);
return v_res_6859_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6860_, lean_object* v_srcJob_6861_, lean_object* v_weakArgs_6862_, lean_object* v_traceArgs_6863_, lean_object* v_leanIncludeDir_x3f_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_){
_start:
{
lean_object* v___f_6872_; lean_object* v___x_6873_; lean_object* v___x_6874_; uint8_t v___x_6875_; lean_object* v___x_6876_; 
v___f_6872_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6872_, 0, v_weakArgs_6862_);
lean_closure_set(v___f_6872_, 1, v_traceArgs_6863_);
lean_closure_set(v___f_6872_, 2, v_oFile_6860_);
lean_closure_set(v___f_6872_, 3, v_leanIncludeDir_x3f_6864_);
v___x_6873_ = l_Lake_instDataKindFilePath;
v___x_6874_ = lean_unsigned_to_nat(0u);
v___x_6875_ = 0;
v___x_6876_ = l_Lake_Job_mapM___redArg(v___x_6873_, v_srcJob_6861_, v___f_6872_, v___x_6874_, v___x_6875_, v_a_6865_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_);
return v___x_6876_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6877_, lean_object* v_srcJob_6878_, lean_object* v_weakArgs_6879_, lean_object* v_traceArgs_6880_, lean_object* v_leanIncludeDir_x3f_6881_, lean_object* v_a_6882_, lean_object* v_a_6883_, lean_object* v_a_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_, lean_object* v_a_6887_, lean_object* v_a_6888_){
_start:
{
lean_object* v_res_6889_; 
v_res_6889_ = l_Lake_buildLeanO(v_oFile_6877_, v_srcJob_6878_, v_weakArgs_6879_, v_traceArgs_6880_, v_leanIncludeDir_x3f_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_);
lean_dec_ref(v_a_6887_);
lean_dec_ref(v_a_6886_);
lean_dec(v_a_6885_);
lean_dec(v_a_6884_);
lean_dec(v_a_6883_);
return v_res_6889_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6890_, lean_object* v_oFiles_6891_, uint8_t v_thin_6892_, lean_object* v___y_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_){
_start:
{
lean_object* v_toContext_6900_; lean_object* v_lakeEnv_6901_; lean_object* v_lean_6902_; lean_object* v_log_6903_; uint8_t v_action_6904_; uint8_t v_wantsRebuild_6905_; lean_object* v_trace_6906_; lean_object* v_buildTime_6907_; lean_object* v___x_6909_; uint8_t v_isShared_6910_; uint8_t v_isSharedCheck_6937_; 
v_toContext_6900_ = lean_ctor_get(v___y_6897_, 1);
v_lakeEnv_6901_ = lean_ctor_get(v_toContext_6900_, 0);
v_lean_6902_ = lean_ctor_get(v_lakeEnv_6901_, 1);
v_log_6903_ = lean_ctor_get(v___y_6898_, 0);
v_action_6904_ = lean_ctor_get_uint8(v___y_6898_, sizeof(void*)*3);
v_wantsRebuild_6905_ = lean_ctor_get_uint8(v___y_6898_, sizeof(void*)*3 + 1);
v_trace_6906_ = lean_ctor_get(v___y_6898_, 1);
v_buildTime_6907_ = lean_ctor_get(v___y_6898_, 2);
v_isSharedCheck_6937_ = !lean_is_exclusive(v___y_6898_);
if (v_isSharedCheck_6937_ == 0)
{
v___x_6909_ = v___y_6898_;
v_isShared_6910_ = v_isSharedCheck_6937_;
goto v_resetjp_6908_;
}
else
{
lean_inc(v_buildTime_6907_);
lean_inc(v_trace_6906_);
lean_inc(v_log_6903_);
lean_dec(v___y_6898_);
v___x_6909_ = lean_box(0);
v_isShared_6910_ = v_isSharedCheck_6937_;
goto v_resetjp_6908_;
}
v_resetjp_6908_:
{
lean_object* v_ar_6911_; lean_object* v___x_6912_; 
v_ar_6911_ = lean_ctor_get(v_lean_6902_, 13);
lean_inc_ref(v_ar_6911_);
v___x_6912_ = l_Lake_compileStaticLib(v_libFile_6890_, v_oFiles_6891_, v_ar_6911_, v_thin_6892_, v_log_6903_);
if (lean_obj_tag(v___x_6912_) == 0)
{
lean_object* v_a_6913_; lean_object* v_a_6914_; lean_object* v___x_6916_; uint8_t v_isShared_6917_; uint8_t v_isSharedCheck_6924_; 
v_a_6913_ = lean_ctor_get(v___x_6912_, 0);
v_a_6914_ = lean_ctor_get(v___x_6912_, 1);
v_isSharedCheck_6924_ = !lean_is_exclusive(v___x_6912_);
if (v_isSharedCheck_6924_ == 0)
{
v___x_6916_ = v___x_6912_;
v_isShared_6917_ = v_isSharedCheck_6924_;
goto v_resetjp_6915_;
}
else
{
lean_inc(v_a_6914_);
lean_inc(v_a_6913_);
lean_dec(v___x_6912_);
v___x_6916_ = lean_box(0);
v_isShared_6917_ = v_isSharedCheck_6924_;
goto v_resetjp_6915_;
}
v_resetjp_6915_:
{
lean_object* v___x_6919_; 
if (v_isShared_6910_ == 0)
{
lean_ctor_set(v___x_6909_, 0, v_a_6914_);
v___x_6919_ = v___x_6909_;
goto v_reusejp_6918_;
}
else
{
lean_object* v_reuseFailAlloc_6923_; 
v_reuseFailAlloc_6923_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6914_);
lean_ctor_set(v_reuseFailAlloc_6923_, 1, v_trace_6906_);
lean_ctor_set(v_reuseFailAlloc_6923_, 2, v_buildTime_6907_);
lean_ctor_set_uint8(v_reuseFailAlloc_6923_, sizeof(void*)*3, v_action_6904_);
lean_ctor_set_uint8(v_reuseFailAlloc_6923_, sizeof(void*)*3 + 1, v_wantsRebuild_6905_);
v___x_6919_ = v_reuseFailAlloc_6923_;
goto v_reusejp_6918_;
}
v_reusejp_6918_:
{
lean_object* v___x_6921_; 
if (v_isShared_6917_ == 0)
{
lean_ctor_set(v___x_6916_, 1, v___x_6919_);
v___x_6921_ = v___x_6916_;
goto v_reusejp_6920_;
}
else
{
lean_object* v_reuseFailAlloc_6922_; 
v_reuseFailAlloc_6922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_a_6913_);
lean_ctor_set(v_reuseFailAlloc_6922_, 1, v___x_6919_);
v___x_6921_ = v_reuseFailAlloc_6922_;
goto v_reusejp_6920_;
}
v_reusejp_6920_:
{
return v___x_6921_;
}
}
}
}
else
{
lean_object* v_a_6925_; lean_object* v_a_6926_; lean_object* v___x_6928_; uint8_t v_isShared_6929_; uint8_t v_isSharedCheck_6936_; 
v_a_6925_ = lean_ctor_get(v___x_6912_, 0);
v_a_6926_ = lean_ctor_get(v___x_6912_, 1);
v_isSharedCheck_6936_ = !lean_is_exclusive(v___x_6912_);
if (v_isSharedCheck_6936_ == 0)
{
v___x_6928_ = v___x_6912_;
v_isShared_6929_ = v_isSharedCheck_6936_;
goto v_resetjp_6927_;
}
else
{
lean_inc(v_a_6926_);
lean_inc(v_a_6925_);
lean_dec(v___x_6912_);
v___x_6928_ = lean_box(0);
v_isShared_6929_ = v_isSharedCheck_6936_;
goto v_resetjp_6927_;
}
v_resetjp_6927_:
{
lean_object* v___x_6931_; 
if (v_isShared_6910_ == 0)
{
lean_ctor_set(v___x_6909_, 0, v_a_6926_);
v___x_6931_ = v___x_6909_;
goto v_reusejp_6930_;
}
else
{
lean_object* v_reuseFailAlloc_6935_; 
v_reuseFailAlloc_6935_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_a_6926_);
lean_ctor_set(v_reuseFailAlloc_6935_, 1, v_trace_6906_);
lean_ctor_set(v_reuseFailAlloc_6935_, 2, v_buildTime_6907_);
lean_ctor_set_uint8(v_reuseFailAlloc_6935_, sizeof(void*)*3, v_action_6904_);
lean_ctor_set_uint8(v_reuseFailAlloc_6935_, sizeof(void*)*3 + 1, v_wantsRebuild_6905_);
v___x_6931_ = v_reuseFailAlloc_6935_;
goto v_reusejp_6930_;
}
v_reusejp_6930_:
{
lean_object* v___x_6933_; 
if (v_isShared_6929_ == 0)
{
lean_ctor_set(v___x_6928_, 1, v___x_6931_);
v___x_6933_ = v___x_6928_;
goto v_reusejp_6932_;
}
else
{
lean_object* v_reuseFailAlloc_6934_; 
v_reuseFailAlloc_6934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6934_, 0, v_a_6925_);
lean_ctor_set(v_reuseFailAlloc_6934_, 1, v___x_6931_);
v___x_6933_ = v_reuseFailAlloc_6934_;
goto v_reusejp_6932_;
}
v_reusejp_6932_:
{
return v___x_6933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6938_, lean_object* v_oFiles_6939_, lean_object* v_thin_6940_, lean_object* v___y_6941_, lean_object* v___y_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_){
_start:
{
uint8_t v_thin_boxed_6948_; lean_object* v_res_6949_; 
v_thin_boxed_6948_ = lean_unbox(v_thin_6940_);
v_res_6949_ = l_Lake_buildStaticLib___lam__0(v_libFile_6938_, v_oFiles_6939_, v_thin_boxed_6948_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_);
lean_dec_ref(v___y_6945_);
lean_dec(v___y_6944_);
lean_dec(v___y_6943_);
lean_dec(v___y_6942_);
lean_dec_ref(v___y_6941_);
return v_res_6949_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6951_, uint8_t v_thin_6952_, lean_object* v_oFiles_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_){
_start:
{
lean_object* v___x_6961_; lean_object* v___f_6962_; uint8_t v___x_6963_; lean_object* v___x_6964_; uint8_t v___x_6965_; lean_object* v___x_6966_; 
v___x_6961_ = lean_box(v_thin_6952_);
lean_inc_ref(v_libFile_6951_);
v___f_6962_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6962_, 0, v_libFile_6951_);
lean_closure_set(v___f_6962_, 1, v_oFiles_6953_);
lean_closure_set(v___f_6962_, 2, v___x_6961_);
v___x_6963_ = 0;
v___x_6964_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6965_ = 1;
v___x_6966_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6951_, v___f_6962_, v___x_6963_, v___x_6964_, v___x_6965_, v___x_6963_, v___x_6963_, v___y_6954_, v___y_6955_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_);
if (lean_obj_tag(v___x_6966_) == 0)
{
lean_object* v_a_6967_; lean_object* v_a_6968_; lean_object* v___x_6970_; uint8_t v_isShared_6971_; uint8_t v_isSharedCheck_6976_; 
v_a_6967_ = lean_ctor_get(v___x_6966_, 0);
v_a_6968_ = lean_ctor_get(v___x_6966_, 1);
v_isSharedCheck_6976_ = !lean_is_exclusive(v___x_6966_);
if (v_isSharedCheck_6976_ == 0)
{
v___x_6970_ = v___x_6966_;
v_isShared_6971_ = v_isSharedCheck_6976_;
goto v_resetjp_6969_;
}
else
{
lean_inc(v_a_6968_);
lean_inc(v_a_6967_);
lean_dec(v___x_6966_);
v___x_6970_ = lean_box(0);
v_isShared_6971_ = v_isSharedCheck_6976_;
goto v_resetjp_6969_;
}
v_resetjp_6969_:
{
lean_object* v_path_6972_; lean_object* v___x_6974_; 
v_path_6972_ = lean_ctor_get(v_a_6967_, 1);
lean_inc_ref(v_path_6972_);
lean_dec(v_a_6967_);
if (v_isShared_6971_ == 0)
{
lean_ctor_set(v___x_6970_, 0, v_path_6972_);
v___x_6974_ = v___x_6970_;
goto v_reusejp_6973_;
}
else
{
lean_object* v_reuseFailAlloc_6975_; 
v_reuseFailAlloc_6975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6975_, 0, v_path_6972_);
lean_ctor_set(v_reuseFailAlloc_6975_, 1, v_a_6968_);
v___x_6974_ = v_reuseFailAlloc_6975_;
goto v_reusejp_6973_;
}
v_reusejp_6973_:
{
return v___x_6974_;
}
}
}
else
{
lean_object* v_a_6977_; lean_object* v_a_6978_; lean_object* v___x_6980_; uint8_t v_isShared_6981_; uint8_t v_isSharedCheck_6985_; 
v_a_6977_ = lean_ctor_get(v___x_6966_, 0);
v_a_6978_ = lean_ctor_get(v___x_6966_, 1);
v_isSharedCheck_6985_ = !lean_is_exclusive(v___x_6966_);
if (v_isSharedCheck_6985_ == 0)
{
v___x_6980_ = v___x_6966_;
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
else
{
lean_inc(v_a_6978_);
lean_inc(v_a_6977_);
lean_dec(v___x_6966_);
v___x_6980_ = lean_box(0);
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
v_resetjp_6979_:
{
lean_object* v___x_6983_; 
if (v_isShared_6981_ == 0)
{
v___x_6983_ = v___x_6980_;
goto v_reusejp_6982_;
}
else
{
lean_object* v_reuseFailAlloc_6984_; 
v_reuseFailAlloc_6984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_a_6977_);
lean_ctor_set(v_reuseFailAlloc_6984_, 1, v_a_6978_);
v___x_6983_ = v_reuseFailAlloc_6984_;
goto v_reusejp_6982_;
}
v_reusejp_6982_:
{
return v___x_6983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6986_, lean_object* v_thin_6987_, lean_object* v_oFiles_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_){
_start:
{
uint8_t v_thin_boxed_6996_; lean_object* v_res_6997_; 
v_thin_boxed_6996_ = lean_unbox(v_thin_6987_);
v_res_6997_ = l_Lake_buildStaticLib___lam__1(v_libFile_6986_, v_thin_boxed_6996_, v_oFiles_6988_, v___y_6989_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_);
lean_dec_ref(v___y_6993_);
lean_dec(v___y_6992_);
lean_dec(v___y_6991_);
lean_dec(v___y_6990_);
return v_res_6997_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6999_, lean_object* v_oFileJobs_7000_, uint8_t v_thin_7001_, lean_object* v_a_7002_, lean_object* v_a_7003_, lean_object* v_a_7004_, lean_object* v_a_7005_, lean_object* v_a_7006_, lean_object* v_a_7007_){
_start:
{
lean_object* v___x_7009_; lean_object* v___f_7010_; lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7014_; uint8_t v___x_7015_; lean_object* v___x_7016_; 
v___x_7009_ = lean_box(v_thin_7001_);
v___f_7010_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_7010_, 0, v_libFile_6999_);
lean_closure_set(v___f_7010_, 1, v___x_7009_);
v___x_7011_ = l_Lake_instDataKindFilePath;
v___x_7012_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_7013_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_7000_, v___x_7012_);
v___x_7014_ = lean_unsigned_to_nat(0u);
v___x_7015_ = 0;
v___x_7016_ = l_Lake_Job_mapM___redArg(v___x_7011_, v___x_7013_, v___f_7010_, v___x_7014_, v___x_7015_, v_a_7002_, v_a_7003_, v_a_7004_, v_a_7005_, v_a_7006_, v_a_7007_);
return v___x_7016_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_7017_, lean_object* v_oFileJobs_7018_, lean_object* v_thin_7019_, lean_object* v_a_7020_, lean_object* v_a_7021_, lean_object* v_a_7022_, lean_object* v_a_7023_, lean_object* v_a_7024_, lean_object* v_a_7025_, lean_object* v_a_7026_){
_start:
{
uint8_t v_thin_boxed_7027_; lean_object* v_res_7028_; 
v_thin_boxed_7027_ = lean_unbox(v_thin_7019_);
v_res_7028_ = l_Lake_buildStaticLib(v_libFile_7017_, v_oFileJobs_7018_, v_thin_boxed_7027_, v_a_7020_, v_a_7021_, v_a_7022_, v_a_7023_, v_a_7024_, v_a_7025_);
lean_dec_ref(v_a_7025_);
lean_dec_ref(v_a_7024_);
lean_dec(v_a_7023_);
lean_dec(v_a_7022_);
lean_dec(v_a_7021_);
lean_dec_ref(v_oFileJobs_7018_);
return v_res_7028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7029_, size_t v_sz_7030_, size_t v_i_7031_, lean_object* v_b_7032_){
_start:
{
uint8_t v___x_7033_; 
v___x_7033_ = lean_usize_dec_lt(v_i_7031_, v_sz_7030_);
if (v___x_7033_ == 0)
{
return v_b_7032_;
}
else
{
lean_object* v_a_7034_; lean_object* v___x_7035_; size_t v___x_7036_; size_t v___x_7037_; 
v_a_7034_ = lean_array_uget_borrowed(v_as_7029_, v_i_7031_);
lean_inc(v_a_7034_);
v___x_7035_ = lean_array_push(v_b_7032_, v_a_7034_);
v___x_7036_ = ((size_t)1ULL);
v___x_7037_ = lean_usize_add(v_i_7031_, v___x_7036_);
v_i_7031_ = v___x_7037_;
v_b_7032_ = v___x_7035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7039_, lean_object* v_sz_7040_, lean_object* v_i_7041_, lean_object* v_b_7042_){
_start:
{
size_t v_sz_boxed_7043_; size_t v_i_boxed_7044_; lean_object* v_res_7045_; 
v_sz_boxed_7043_ = lean_unbox_usize(v_sz_7040_);
lean_dec(v_sz_7040_);
v_i_boxed_7044_ = lean_unbox_usize(v_i_7041_);
lean_dec(v_i_7041_);
v_res_7045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7039_, v_sz_boxed_7043_, v_i_boxed_7044_, v_b_7042_);
lean_dec_ref(v_as_7039_);
return v_res_7045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7048_, size_t v_sz_7049_, size_t v_i_7050_, lean_object* v_b_7051_){
_start:
{
uint8_t v___x_7052_; 
v___x_7052_ = lean_usize_dec_lt(v_i_7050_, v_sz_7049_);
if (v___x_7052_ == 0)
{
return v_b_7051_;
}
else
{
lean_object* v_a_7053_; lean_object* v_args_7055_; lean_object* v___x_7063_; 
v_a_7053_ = lean_array_uget_borrowed(v_as_7048_, v_i_7050_);
lean_inc(v_a_7053_);
v___x_7063_ = l_Lake_Dynlib_dir_x3f(v_a_7053_);
if (lean_obj_tag(v___x_7063_) == 1)
{
lean_object* v_val_7064_; lean_object* v___x_7065_; lean_object* v___x_7066_; lean_object* v___x_7067_; 
v_val_7064_ = lean_ctor_get(v___x_7063_, 0);
lean_inc(v_val_7064_);
lean_dec_ref_known(v___x_7063_, 1);
v___x_7065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7066_ = lean_string_append(v___x_7065_, v_val_7064_);
lean_dec(v_val_7064_);
v___x_7067_ = lean_array_push(v_b_7051_, v___x_7066_);
v_args_7055_ = v___x_7067_;
goto v___jp_7054_;
}
else
{
lean_dec(v___x_7063_);
v_args_7055_ = v_b_7051_;
goto v___jp_7054_;
}
v___jp_7054_:
{
lean_object* v_name_7056_; lean_object* v___x_7057_; lean_object* v___x_7058_; lean_object* v___x_7059_; size_t v___x_7060_; size_t v___x_7061_; 
v_name_7056_ = lean_ctor_get(v_a_7053_, 1);
v___x_7057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7058_ = lean_string_append(v___x_7057_, v_name_7056_);
v___x_7059_ = lean_array_push(v_args_7055_, v___x_7058_);
v___x_7060_ = ((size_t)1ULL);
v___x_7061_ = lean_usize_add(v_i_7050_, v___x_7060_);
v_i_7050_ = v___x_7061_;
v_b_7051_ = v___x_7059_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7068_, lean_object* v_sz_7069_, lean_object* v_i_7070_, lean_object* v_b_7071_){
_start:
{
size_t v_sz_boxed_7072_; size_t v_i_boxed_7073_; lean_object* v_res_7074_; 
v_sz_boxed_7072_ = lean_unbox_usize(v_sz_7069_);
lean_dec(v_sz_7069_);
v_i_boxed_7073_ = lean_unbox_usize(v_i_7070_);
lean_dec(v_i_7070_);
v_res_7074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7068_, v_sz_boxed_7072_, v_i_boxed_7073_, v_b_7071_);
lean_dec_ref(v_as_7068_);
return v_res_7074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7075_, lean_object* v_libs_7076_){
_start:
{
lean_object* v_args_7077_; size_t v_sz_7078_; size_t v___x_7079_; lean_object* v___x_7080_; size_t v_sz_7081_; lean_object* v___x_7082_; 
v_args_7077_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7078_ = lean_array_size(v_objs_7075_);
v___x_7079_ = ((size_t)0ULL);
v___x_7080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7075_, v_sz_7078_, v___x_7079_, v_args_7077_);
v_sz_7081_ = lean_array_size(v_libs_7076_);
v___x_7082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7076_, v_sz_7081_, v___x_7079_, v___x_7080_);
return v___x_7082_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7083_, lean_object* v_libs_7084_){
_start:
{
lean_object* v_res_7085_; 
v_res_7085_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7083_, v_libs_7084_);
lean_dec_ref(v_libs_7084_);
lean_dec_ref(v_objs_7083_);
return v_res_7085_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7086_, lean_object* v_t_7087_){
_start:
{
if (lean_obj_tag(v_t_7087_) == 0)
{
lean_object* v_k_7088_; lean_object* v_l_7089_; lean_object* v_r_7090_; uint8_t v___x_7091_; 
v_k_7088_ = lean_ctor_get(v_t_7087_, 1);
v_l_7089_ = lean_ctor_get(v_t_7087_, 3);
v_r_7090_ = lean_ctor_get(v_t_7087_, 4);
v___x_7091_ = lean_string_compare(v_k_7086_, v_k_7088_);
switch(v___x_7091_)
{
case 0:
{
v_t_7087_ = v_l_7089_;
goto _start;
}
case 1:
{
uint8_t v___x_7093_; 
v___x_7093_ = 1;
return v___x_7093_;
}
default: 
{
v_t_7087_ = v_r_7090_;
goto _start;
}
}
}
else
{
uint8_t v___x_7095_; 
v___x_7095_ = 0;
return v___x_7095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7096_, lean_object* v_t_7097_){
_start:
{
uint8_t v_res_7098_; lean_object* v_r_7099_; 
v_res_7098_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7096_, v_t_7097_);
lean_dec(v_t_7097_);
lean_dec_ref(v_k_7096_);
v_r_7099_ = lean_box(v_res_7098_);
return v_r_7099_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7100_, lean_object* v_x_7101_){
_start:
{
if (lean_obj_tag(v_x_7101_) == 0)
{
uint8_t v___x_7102_; 
v___x_7102_ = 0;
return v___x_7102_;
}
else
{
lean_object* v_head_7103_; lean_object* v_tail_7104_; uint8_t v___x_7105_; 
v_head_7103_ = lean_ctor_get(v_x_7101_, 0);
v_tail_7104_ = lean_ctor_get(v_x_7101_, 1);
v___x_7105_ = lean_string_dec_eq(v_a_7100_, v_head_7103_);
if (v___x_7105_ == 0)
{
v_x_7101_ = v_tail_7104_;
goto _start;
}
else
{
return v___x_7105_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7107_, lean_object* v_x_7108_){
_start:
{
uint8_t v_res_7109_; lean_object* v_r_7110_; 
v_res_7109_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7107_, v_x_7108_);
lean_dec(v_x_7108_);
lean_dec_ref(v_a_7107_);
v_r_7110_ = lean_box(v_res_7109_);
return v_r_7110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7111_, lean_object* v_v_7112_, lean_object* v_t_7113_){
_start:
{
if (lean_obj_tag(v_t_7113_) == 0)
{
lean_object* v_size_7114_; lean_object* v_k_7115_; lean_object* v_v_7116_; lean_object* v_l_7117_; lean_object* v_r_7118_; lean_object* v___x_7120_; uint8_t v_isShared_7121_; uint8_t v_isSharedCheck_7398_; 
v_size_7114_ = lean_ctor_get(v_t_7113_, 0);
v_k_7115_ = lean_ctor_get(v_t_7113_, 1);
v_v_7116_ = lean_ctor_get(v_t_7113_, 2);
v_l_7117_ = lean_ctor_get(v_t_7113_, 3);
v_r_7118_ = lean_ctor_get(v_t_7113_, 4);
v_isSharedCheck_7398_ = !lean_is_exclusive(v_t_7113_);
if (v_isSharedCheck_7398_ == 0)
{
v___x_7120_ = v_t_7113_;
v_isShared_7121_ = v_isSharedCheck_7398_;
goto v_resetjp_7119_;
}
else
{
lean_inc(v_r_7118_);
lean_inc(v_l_7117_);
lean_inc(v_v_7116_);
lean_inc(v_k_7115_);
lean_inc(v_size_7114_);
lean_dec(v_t_7113_);
v___x_7120_ = lean_box(0);
v_isShared_7121_ = v_isSharedCheck_7398_;
goto v_resetjp_7119_;
}
v_resetjp_7119_:
{
uint8_t v___x_7122_; 
v___x_7122_ = lean_string_compare(v_k_7111_, v_k_7115_);
switch(v___x_7122_)
{
case 0:
{
lean_object* v_impl_7123_; lean_object* v___x_7124_; 
lean_dec(v_size_7114_);
v_impl_7123_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7111_, v_v_7112_, v_l_7117_);
v___x_7124_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7118_) == 0)
{
lean_object* v_size_7125_; lean_object* v_size_7126_; lean_object* v_k_7127_; lean_object* v_v_7128_; lean_object* v_l_7129_; lean_object* v_r_7130_; lean_object* v___x_7131_; lean_object* v___x_7132_; uint8_t v___x_7133_; 
v_size_7125_ = lean_ctor_get(v_r_7118_, 0);
v_size_7126_ = lean_ctor_get(v_impl_7123_, 0);
lean_inc(v_size_7126_);
v_k_7127_ = lean_ctor_get(v_impl_7123_, 1);
lean_inc(v_k_7127_);
v_v_7128_ = lean_ctor_get(v_impl_7123_, 2);
lean_inc(v_v_7128_);
v_l_7129_ = lean_ctor_get(v_impl_7123_, 3);
lean_inc(v_l_7129_);
v_r_7130_ = lean_ctor_get(v_impl_7123_, 4);
lean_inc(v_r_7130_);
v___x_7131_ = lean_unsigned_to_nat(3u);
v___x_7132_ = lean_nat_mul(v___x_7131_, v_size_7125_);
v___x_7133_ = lean_nat_dec_lt(v___x_7132_, v_size_7126_);
lean_dec(v___x_7132_);
if (v___x_7133_ == 0)
{
lean_object* v___x_7134_; lean_object* v___x_7135_; lean_object* v___x_7137_; 
lean_dec(v_r_7130_);
lean_dec(v_l_7129_);
lean_dec(v_v_7128_);
lean_dec(v_k_7127_);
v___x_7134_ = lean_nat_add(v___x_7124_, v_size_7126_);
lean_dec(v_size_7126_);
v___x_7135_ = lean_nat_add(v___x_7134_, v_size_7125_);
lean_dec(v___x_7134_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
lean_ctor_set(v___x_7120_, 0, v___x_7135_);
v___x_7137_ = v___x_7120_;
goto v_reusejp_7136_;
}
else
{
lean_object* v_reuseFailAlloc_7138_; 
v_reuseFailAlloc_7138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7138_, 0, v___x_7135_);
lean_ctor_set(v_reuseFailAlloc_7138_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7138_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7138_, 3, v_impl_7123_);
lean_ctor_set(v_reuseFailAlloc_7138_, 4, v_r_7118_);
v___x_7137_ = v_reuseFailAlloc_7138_;
goto v_reusejp_7136_;
}
v_reusejp_7136_:
{
return v___x_7137_;
}
}
else
{
lean_object* v___x_7140_; uint8_t v_isShared_7141_; uint8_t v_isSharedCheck_7204_; 
v_isSharedCheck_7204_ = !lean_is_exclusive(v_impl_7123_);
if (v_isSharedCheck_7204_ == 0)
{
lean_object* v_unused_7205_; lean_object* v_unused_7206_; lean_object* v_unused_7207_; lean_object* v_unused_7208_; lean_object* v_unused_7209_; 
v_unused_7205_ = lean_ctor_get(v_impl_7123_, 4);
lean_dec(v_unused_7205_);
v_unused_7206_ = lean_ctor_get(v_impl_7123_, 3);
lean_dec(v_unused_7206_);
v_unused_7207_ = lean_ctor_get(v_impl_7123_, 2);
lean_dec(v_unused_7207_);
v_unused_7208_ = lean_ctor_get(v_impl_7123_, 1);
lean_dec(v_unused_7208_);
v_unused_7209_ = lean_ctor_get(v_impl_7123_, 0);
lean_dec(v_unused_7209_);
v___x_7140_ = v_impl_7123_;
v_isShared_7141_ = v_isSharedCheck_7204_;
goto v_resetjp_7139_;
}
else
{
lean_dec(v_impl_7123_);
v___x_7140_ = lean_box(0);
v_isShared_7141_ = v_isSharedCheck_7204_;
goto v_resetjp_7139_;
}
v_resetjp_7139_:
{
lean_object* v_size_7142_; lean_object* v_size_7143_; lean_object* v_k_7144_; lean_object* v_v_7145_; lean_object* v_l_7146_; lean_object* v_r_7147_; lean_object* v___x_7148_; lean_object* v___x_7149_; uint8_t v___x_7150_; 
v_size_7142_ = lean_ctor_get(v_l_7129_, 0);
v_size_7143_ = lean_ctor_get(v_r_7130_, 0);
v_k_7144_ = lean_ctor_get(v_r_7130_, 1);
v_v_7145_ = lean_ctor_get(v_r_7130_, 2);
v_l_7146_ = lean_ctor_get(v_r_7130_, 3);
v_r_7147_ = lean_ctor_get(v_r_7130_, 4);
v___x_7148_ = lean_unsigned_to_nat(2u);
v___x_7149_ = lean_nat_mul(v___x_7148_, v_size_7142_);
v___x_7150_ = lean_nat_dec_lt(v_size_7143_, v___x_7149_);
lean_dec(v___x_7149_);
if (v___x_7150_ == 0)
{
lean_object* v___x_7152_; uint8_t v_isShared_7153_; uint8_t v_isSharedCheck_7179_; 
lean_inc(v_r_7147_);
lean_inc(v_l_7146_);
lean_inc(v_v_7145_);
lean_inc(v_k_7144_);
v_isSharedCheck_7179_ = !lean_is_exclusive(v_r_7130_);
if (v_isSharedCheck_7179_ == 0)
{
lean_object* v_unused_7180_; lean_object* v_unused_7181_; lean_object* v_unused_7182_; lean_object* v_unused_7183_; lean_object* v_unused_7184_; 
v_unused_7180_ = lean_ctor_get(v_r_7130_, 4);
lean_dec(v_unused_7180_);
v_unused_7181_ = lean_ctor_get(v_r_7130_, 3);
lean_dec(v_unused_7181_);
v_unused_7182_ = lean_ctor_get(v_r_7130_, 2);
lean_dec(v_unused_7182_);
v_unused_7183_ = lean_ctor_get(v_r_7130_, 1);
lean_dec(v_unused_7183_);
v_unused_7184_ = lean_ctor_get(v_r_7130_, 0);
lean_dec(v_unused_7184_);
v___x_7152_ = v_r_7130_;
v_isShared_7153_ = v_isSharedCheck_7179_;
goto v_resetjp_7151_;
}
else
{
lean_dec(v_r_7130_);
v___x_7152_ = lean_box(0);
v_isShared_7153_ = v_isSharedCheck_7179_;
goto v_resetjp_7151_;
}
v_resetjp_7151_:
{
lean_object* v___x_7154_; lean_object* v___x_7155_; lean_object* v___y_7157_; lean_object* v___y_7158_; lean_object* v___y_7159_; lean_object* v___x_7167_; lean_object* v___y_7169_; 
v___x_7154_ = lean_nat_add(v___x_7124_, v_size_7126_);
lean_dec(v_size_7126_);
v___x_7155_ = lean_nat_add(v___x_7154_, v_size_7125_);
lean_dec(v___x_7154_);
v___x_7167_ = lean_nat_add(v___x_7124_, v_size_7142_);
if (lean_obj_tag(v_l_7146_) == 0)
{
lean_object* v_size_7177_; 
v_size_7177_ = lean_ctor_get(v_l_7146_, 0);
lean_inc(v_size_7177_);
v___y_7169_ = v_size_7177_;
goto v___jp_7168_;
}
else
{
lean_object* v___x_7178_; 
v___x_7178_ = lean_unsigned_to_nat(0u);
v___y_7169_ = v___x_7178_;
goto v___jp_7168_;
}
v___jp_7156_:
{
lean_object* v___x_7160_; lean_object* v___x_7162_; 
v___x_7160_ = lean_nat_add(v___y_7157_, v___y_7159_);
lean_dec(v___y_7159_);
lean_dec(v___y_7157_);
if (v_isShared_7153_ == 0)
{
lean_ctor_set(v___x_7152_, 4, v_r_7118_);
lean_ctor_set(v___x_7152_, 3, v_r_7147_);
lean_ctor_set(v___x_7152_, 2, v_v_7116_);
lean_ctor_set(v___x_7152_, 1, v_k_7115_);
lean_ctor_set(v___x_7152_, 0, v___x_7160_);
v___x_7162_ = v___x_7152_;
goto v_reusejp_7161_;
}
else
{
lean_object* v_reuseFailAlloc_7166_; 
v_reuseFailAlloc_7166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7166_, 0, v___x_7160_);
lean_ctor_set(v_reuseFailAlloc_7166_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7166_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7166_, 3, v_r_7147_);
lean_ctor_set(v_reuseFailAlloc_7166_, 4, v_r_7118_);
v___x_7162_ = v_reuseFailAlloc_7166_;
goto v_reusejp_7161_;
}
v_reusejp_7161_:
{
lean_object* v___x_7164_; 
if (v_isShared_7141_ == 0)
{
lean_ctor_set(v___x_7140_, 4, v___x_7162_);
lean_ctor_set(v___x_7140_, 3, v___y_7158_);
lean_ctor_set(v___x_7140_, 2, v_v_7145_);
lean_ctor_set(v___x_7140_, 1, v_k_7144_);
lean_ctor_set(v___x_7140_, 0, v___x_7155_);
v___x_7164_ = v___x_7140_;
goto v_reusejp_7163_;
}
else
{
lean_object* v_reuseFailAlloc_7165_; 
v_reuseFailAlloc_7165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7165_, 0, v___x_7155_);
lean_ctor_set(v_reuseFailAlloc_7165_, 1, v_k_7144_);
lean_ctor_set(v_reuseFailAlloc_7165_, 2, v_v_7145_);
lean_ctor_set(v_reuseFailAlloc_7165_, 3, v___y_7158_);
lean_ctor_set(v_reuseFailAlloc_7165_, 4, v___x_7162_);
v___x_7164_ = v_reuseFailAlloc_7165_;
goto v_reusejp_7163_;
}
v_reusejp_7163_:
{
return v___x_7164_;
}
}
}
v___jp_7168_:
{
lean_object* v___x_7170_; lean_object* v___x_7172_; 
v___x_7170_ = lean_nat_add(v___x_7167_, v___y_7169_);
lean_dec(v___y_7169_);
lean_dec(v___x_7167_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_l_7146_);
lean_ctor_set(v___x_7120_, 3, v_l_7129_);
lean_ctor_set(v___x_7120_, 2, v_v_7128_);
lean_ctor_set(v___x_7120_, 1, v_k_7127_);
lean_ctor_set(v___x_7120_, 0, v___x_7170_);
v___x_7172_ = v___x_7120_;
goto v_reusejp_7171_;
}
else
{
lean_object* v_reuseFailAlloc_7176_; 
v_reuseFailAlloc_7176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7176_, 0, v___x_7170_);
lean_ctor_set(v_reuseFailAlloc_7176_, 1, v_k_7127_);
lean_ctor_set(v_reuseFailAlloc_7176_, 2, v_v_7128_);
lean_ctor_set(v_reuseFailAlloc_7176_, 3, v_l_7129_);
lean_ctor_set(v_reuseFailAlloc_7176_, 4, v_l_7146_);
v___x_7172_ = v_reuseFailAlloc_7176_;
goto v_reusejp_7171_;
}
v_reusejp_7171_:
{
lean_object* v___x_7173_; 
v___x_7173_ = lean_nat_add(v___x_7124_, v_size_7125_);
if (lean_obj_tag(v_r_7147_) == 0)
{
lean_object* v_size_7174_; 
v_size_7174_ = lean_ctor_get(v_r_7147_, 0);
lean_inc(v_size_7174_);
v___y_7157_ = v___x_7173_;
v___y_7158_ = v___x_7172_;
v___y_7159_ = v_size_7174_;
goto v___jp_7156_;
}
else
{
lean_object* v___x_7175_; 
v___x_7175_ = lean_unsigned_to_nat(0u);
v___y_7157_ = v___x_7173_;
v___y_7158_ = v___x_7172_;
v___y_7159_ = v___x_7175_;
goto v___jp_7156_;
}
}
}
}
}
else
{
lean_object* v___x_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7190_; 
lean_del_object(v___x_7120_);
v___x_7185_ = lean_nat_add(v___x_7124_, v_size_7126_);
lean_dec(v_size_7126_);
v___x_7186_ = lean_nat_add(v___x_7185_, v_size_7125_);
lean_dec(v___x_7185_);
v___x_7187_ = lean_nat_add(v___x_7124_, v_size_7125_);
v___x_7188_ = lean_nat_add(v___x_7187_, v_size_7143_);
lean_dec(v___x_7187_);
lean_inc_ref(v_r_7118_);
if (v_isShared_7141_ == 0)
{
lean_ctor_set(v___x_7140_, 4, v_r_7118_);
lean_ctor_set(v___x_7140_, 3, v_r_7130_);
lean_ctor_set(v___x_7140_, 2, v_v_7116_);
lean_ctor_set(v___x_7140_, 1, v_k_7115_);
lean_ctor_set(v___x_7140_, 0, v___x_7188_);
v___x_7190_ = v___x_7140_;
goto v_reusejp_7189_;
}
else
{
lean_object* v_reuseFailAlloc_7203_; 
v_reuseFailAlloc_7203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7203_, 0, v___x_7188_);
lean_ctor_set(v_reuseFailAlloc_7203_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7203_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7203_, 3, v_r_7130_);
lean_ctor_set(v_reuseFailAlloc_7203_, 4, v_r_7118_);
v___x_7190_ = v_reuseFailAlloc_7203_;
goto v_reusejp_7189_;
}
v_reusejp_7189_:
{
lean_object* v___x_7192_; uint8_t v_isShared_7193_; uint8_t v_isSharedCheck_7197_; 
v_isSharedCheck_7197_ = !lean_is_exclusive(v_r_7118_);
if (v_isSharedCheck_7197_ == 0)
{
lean_object* v_unused_7198_; lean_object* v_unused_7199_; lean_object* v_unused_7200_; lean_object* v_unused_7201_; lean_object* v_unused_7202_; 
v_unused_7198_ = lean_ctor_get(v_r_7118_, 4);
lean_dec(v_unused_7198_);
v_unused_7199_ = lean_ctor_get(v_r_7118_, 3);
lean_dec(v_unused_7199_);
v_unused_7200_ = lean_ctor_get(v_r_7118_, 2);
lean_dec(v_unused_7200_);
v_unused_7201_ = lean_ctor_get(v_r_7118_, 1);
lean_dec(v_unused_7201_);
v_unused_7202_ = lean_ctor_get(v_r_7118_, 0);
lean_dec(v_unused_7202_);
v___x_7192_ = v_r_7118_;
v_isShared_7193_ = v_isSharedCheck_7197_;
goto v_resetjp_7191_;
}
else
{
lean_dec(v_r_7118_);
v___x_7192_ = lean_box(0);
v_isShared_7193_ = v_isSharedCheck_7197_;
goto v_resetjp_7191_;
}
v_resetjp_7191_:
{
lean_object* v___x_7195_; 
if (v_isShared_7193_ == 0)
{
lean_ctor_set(v___x_7192_, 4, v___x_7190_);
lean_ctor_set(v___x_7192_, 3, v_l_7129_);
lean_ctor_set(v___x_7192_, 2, v_v_7128_);
lean_ctor_set(v___x_7192_, 1, v_k_7127_);
lean_ctor_set(v___x_7192_, 0, v___x_7186_);
v___x_7195_ = v___x_7192_;
goto v_reusejp_7194_;
}
else
{
lean_object* v_reuseFailAlloc_7196_; 
v_reuseFailAlloc_7196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7196_, 0, v___x_7186_);
lean_ctor_set(v_reuseFailAlloc_7196_, 1, v_k_7127_);
lean_ctor_set(v_reuseFailAlloc_7196_, 2, v_v_7128_);
lean_ctor_set(v_reuseFailAlloc_7196_, 3, v_l_7129_);
lean_ctor_set(v_reuseFailAlloc_7196_, 4, v___x_7190_);
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
}
}
}
else
{
lean_object* v_l_7210_; 
v_l_7210_ = lean_ctor_get(v_impl_7123_, 3);
lean_inc(v_l_7210_);
if (lean_obj_tag(v_l_7210_) == 0)
{
lean_object* v_r_7211_; lean_object* v_k_7212_; lean_object* v_v_7213_; lean_object* v___x_7215_; uint8_t v_isShared_7216_; uint8_t v_isSharedCheck_7224_; 
v_r_7211_ = lean_ctor_get(v_impl_7123_, 4);
v_k_7212_ = lean_ctor_get(v_impl_7123_, 1);
v_v_7213_ = lean_ctor_get(v_impl_7123_, 2);
v_isSharedCheck_7224_ = !lean_is_exclusive(v_impl_7123_);
if (v_isSharedCheck_7224_ == 0)
{
lean_object* v_unused_7225_; lean_object* v_unused_7226_; 
v_unused_7225_ = lean_ctor_get(v_impl_7123_, 3);
lean_dec(v_unused_7225_);
v_unused_7226_ = lean_ctor_get(v_impl_7123_, 0);
lean_dec(v_unused_7226_);
v___x_7215_ = v_impl_7123_;
v_isShared_7216_ = v_isSharedCheck_7224_;
goto v_resetjp_7214_;
}
else
{
lean_inc(v_r_7211_);
lean_inc(v_v_7213_);
lean_inc(v_k_7212_);
lean_dec(v_impl_7123_);
v___x_7215_ = lean_box(0);
v_isShared_7216_ = v_isSharedCheck_7224_;
goto v_resetjp_7214_;
}
v_resetjp_7214_:
{
lean_object* v___x_7217_; lean_object* v___x_7219_; 
v___x_7217_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7211_);
if (v_isShared_7216_ == 0)
{
lean_ctor_set(v___x_7215_, 3, v_r_7211_);
lean_ctor_set(v___x_7215_, 2, v_v_7116_);
lean_ctor_set(v___x_7215_, 1, v_k_7115_);
lean_ctor_set(v___x_7215_, 0, v___x_7124_);
v___x_7219_ = v___x_7215_;
goto v_reusejp_7218_;
}
else
{
lean_object* v_reuseFailAlloc_7223_; 
v_reuseFailAlloc_7223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7223_, 0, v___x_7124_);
lean_ctor_set(v_reuseFailAlloc_7223_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7223_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7223_, 3, v_r_7211_);
lean_ctor_set(v_reuseFailAlloc_7223_, 4, v_r_7211_);
v___x_7219_ = v_reuseFailAlloc_7223_;
goto v_reusejp_7218_;
}
v_reusejp_7218_:
{
lean_object* v___x_7221_; 
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v___x_7219_);
lean_ctor_set(v___x_7120_, 3, v_l_7210_);
lean_ctor_set(v___x_7120_, 2, v_v_7213_);
lean_ctor_set(v___x_7120_, 1, v_k_7212_);
lean_ctor_set(v___x_7120_, 0, v___x_7217_);
v___x_7221_ = v___x_7120_;
goto v_reusejp_7220_;
}
else
{
lean_object* v_reuseFailAlloc_7222_; 
v_reuseFailAlloc_7222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7222_, 0, v___x_7217_);
lean_ctor_set(v_reuseFailAlloc_7222_, 1, v_k_7212_);
lean_ctor_set(v_reuseFailAlloc_7222_, 2, v_v_7213_);
lean_ctor_set(v_reuseFailAlloc_7222_, 3, v_l_7210_);
lean_ctor_set(v_reuseFailAlloc_7222_, 4, v___x_7219_);
v___x_7221_ = v_reuseFailAlloc_7222_;
goto v_reusejp_7220_;
}
v_reusejp_7220_:
{
return v___x_7221_;
}
}
}
}
else
{
lean_object* v_r_7227_; 
v_r_7227_ = lean_ctor_get(v_impl_7123_, 4);
lean_inc(v_r_7227_);
if (lean_obj_tag(v_r_7227_) == 0)
{
lean_object* v_k_7228_; lean_object* v_v_7229_; lean_object* v___x_7231_; uint8_t v_isShared_7232_; uint8_t v_isSharedCheck_7252_; 
v_k_7228_ = lean_ctor_get(v_impl_7123_, 1);
v_v_7229_ = lean_ctor_get(v_impl_7123_, 2);
v_isSharedCheck_7252_ = !lean_is_exclusive(v_impl_7123_);
if (v_isSharedCheck_7252_ == 0)
{
lean_object* v_unused_7253_; lean_object* v_unused_7254_; lean_object* v_unused_7255_; 
v_unused_7253_ = lean_ctor_get(v_impl_7123_, 4);
lean_dec(v_unused_7253_);
v_unused_7254_ = lean_ctor_get(v_impl_7123_, 3);
lean_dec(v_unused_7254_);
v_unused_7255_ = lean_ctor_get(v_impl_7123_, 0);
lean_dec(v_unused_7255_);
v___x_7231_ = v_impl_7123_;
v_isShared_7232_ = v_isSharedCheck_7252_;
goto v_resetjp_7230_;
}
else
{
lean_inc(v_v_7229_);
lean_inc(v_k_7228_);
lean_dec(v_impl_7123_);
v___x_7231_ = lean_box(0);
v_isShared_7232_ = v_isSharedCheck_7252_;
goto v_resetjp_7230_;
}
v_resetjp_7230_:
{
lean_object* v_k_7233_; lean_object* v_v_7234_; lean_object* v___x_7236_; uint8_t v_isShared_7237_; uint8_t v_isSharedCheck_7248_; 
v_k_7233_ = lean_ctor_get(v_r_7227_, 1);
v_v_7234_ = lean_ctor_get(v_r_7227_, 2);
v_isSharedCheck_7248_ = !lean_is_exclusive(v_r_7227_);
if (v_isSharedCheck_7248_ == 0)
{
lean_object* v_unused_7249_; lean_object* v_unused_7250_; lean_object* v_unused_7251_; 
v_unused_7249_ = lean_ctor_get(v_r_7227_, 4);
lean_dec(v_unused_7249_);
v_unused_7250_ = lean_ctor_get(v_r_7227_, 3);
lean_dec(v_unused_7250_);
v_unused_7251_ = lean_ctor_get(v_r_7227_, 0);
lean_dec(v_unused_7251_);
v___x_7236_ = v_r_7227_;
v_isShared_7237_ = v_isSharedCheck_7248_;
goto v_resetjp_7235_;
}
else
{
lean_inc(v_v_7234_);
lean_inc(v_k_7233_);
lean_dec(v_r_7227_);
v___x_7236_ = lean_box(0);
v_isShared_7237_ = v_isSharedCheck_7248_;
goto v_resetjp_7235_;
}
v_resetjp_7235_:
{
lean_object* v___x_7238_; lean_object* v___x_7240_; 
v___x_7238_ = lean_unsigned_to_nat(3u);
if (v_isShared_7237_ == 0)
{
lean_ctor_set(v___x_7236_, 4, v_l_7210_);
lean_ctor_set(v___x_7236_, 3, v_l_7210_);
lean_ctor_set(v___x_7236_, 2, v_v_7229_);
lean_ctor_set(v___x_7236_, 1, v_k_7228_);
lean_ctor_set(v___x_7236_, 0, v___x_7124_);
v___x_7240_ = v___x_7236_;
goto v_reusejp_7239_;
}
else
{
lean_object* v_reuseFailAlloc_7247_; 
v_reuseFailAlloc_7247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7247_, 0, v___x_7124_);
lean_ctor_set(v_reuseFailAlloc_7247_, 1, v_k_7228_);
lean_ctor_set(v_reuseFailAlloc_7247_, 2, v_v_7229_);
lean_ctor_set(v_reuseFailAlloc_7247_, 3, v_l_7210_);
lean_ctor_set(v_reuseFailAlloc_7247_, 4, v_l_7210_);
v___x_7240_ = v_reuseFailAlloc_7247_;
goto v_reusejp_7239_;
}
v_reusejp_7239_:
{
lean_object* v___x_7242_; 
if (v_isShared_7232_ == 0)
{
lean_ctor_set(v___x_7231_, 4, v_l_7210_);
lean_ctor_set(v___x_7231_, 2, v_v_7116_);
lean_ctor_set(v___x_7231_, 1, v_k_7115_);
lean_ctor_set(v___x_7231_, 0, v___x_7124_);
v___x_7242_ = v___x_7231_;
goto v_reusejp_7241_;
}
else
{
lean_object* v_reuseFailAlloc_7246_; 
v_reuseFailAlloc_7246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7246_, 0, v___x_7124_);
lean_ctor_set(v_reuseFailAlloc_7246_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7246_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7246_, 3, v_l_7210_);
lean_ctor_set(v_reuseFailAlloc_7246_, 4, v_l_7210_);
v___x_7242_ = v_reuseFailAlloc_7246_;
goto v_reusejp_7241_;
}
v_reusejp_7241_:
{
lean_object* v___x_7244_; 
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v___x_7242_);
lean_ctor_set(v___x_7120_, 3, v___x_7240_);
lean_ctor_set(v___x_7120_, 2, v_v_7234_);
lean_ctor_set(v___x_7120_, 1, v_k_7233_);
lean_ctor_set(v___x_7120_, 0, v___x_7238_);
v___x_7244_ = v___x_7120_;
goto v_reusejp_7243_;
}
else
{
lean_object* v_reuseFailAlloc_7245_; 
v_reuseFailAlloc_7245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7245_, 0, v___x_7238_);
lean_ctor_set(v_reuseFailAlloc_7245_, 1, v_k_7233_);
lean_ctor_set(v_reuseFailAlloc_7245_, 2, v_v_7234_);
lean_ctor_set(v_reuseFailAlloc_7245_, 3, v___x_7240_);
lean_ctor_set(v_reuseFailAlloc_7245_, 4, v___x_7242_);
v___x_7244_ = v_reuseFailAlloc_7245_;
goto v_reusejp_7243_;
}
v_reusejp_7243_:
{
return v___x_7244_;
}
}
}
}
}
}
else
{
lean_object* v___x_7256_; lean_object* v___x_7258_; 
v___x_7256_ = lean_unsigned_to_nat(2u);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_r_7227_);
lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
lean_ctor_set(v___x_7120_, 0, v___x_7256_);
v___x_7258_ = v___x_7120_;
goto v_reusejp_7257_;
}
else
{
lean_object* v_reuseFailAlloc_7259_; 
v_reuseFailAlloc_7259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7259_, 0, v___x_7256_);
lean_ctor_set(v_reuseFailAlloc_7259_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7259_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7259_, 3, v_impl_7123_);
lean_ctor_set(v_reuseFailAlloc_7259_, 4, v_r_7227_);
v___x_7258_ = v_reuseFailAlloc_7259_;
goto v_reusejp_7257_;
}
v_reusejp_7257_:
{
return v___x_7258_;
}
}
}
}
}
case 1:
{
lean_object* v___x_7261_; 
lean_dec(v_v_7116_);
lean_dec(v_k_7115_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 2, v_v_7112_);
lean_ctor_set(v___x_7120_, 1, v_k_7111_);
v___x_7261_ = v___x_7120_;
goto v_reusejp_7260_;
}
else
{
lean_object* v_reuseFailAlloc_7262_; 
v_reuseFailAlloc_7262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7262_, 0, v_size_7114_);
lean_ctor_set(v_reuseFailAlloc_7262_, 1, v_k_7111_);
lean_ctor_set(v_reuseFailAlloc_7262_, 2, v_v_7112_);
lean_ctor_set(v_reuseFailAlloc_7262_, 3, v_l_7117_);
lean_ctor_set(v_reuseFailAlloc_7262_, 4, v_r_7118_);
v___x_7261_ = v_reuseFailAlloc_7262_;
goto v_reusejp_7260_;
}
v_reusejp_7260_:
{
return v___x_7261_;
}
}
default: 
{
lean_object* v_impl_7263_; lean_object* v___x_7264_; 
lean_dec(v_size_7114_);
v_impl_7263_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7111_, v_v_7112_, v_r_7118_);
v___x_7264_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7117_) == 0)
{
lean_object* v_size_7265_; lean_object* v_size_7266_; lean_object* v_k_7267_; lean_object* v_v_7268_; lean_object* v_l_7269_; lean_object* v_r_7270_; lean_object* v___x_7271_; lean_object* v___x_7272_; uint8_t v___x_7273_; 
v_size_7265_ = lean_ctor_get(v_l_7117_, 0);
v_size_7266_ = lean_ctor_get(v_impl_7263_, 0);
lean_inc(v_size_7266_);
v_k_7267_ = lean_ctor_get(v_impl_7263_, 1);
lean_inc(v_k_7267_);
v_v_7268_ = lean_ctor_get(v_impl_7263_, 2);
lean_inc(v_v_7268_);
v_l_7269_ = lean_ctor_get(v_impl_7263_, 3);
lean_inc(v_l_7269_);
v_r_7270_ = lean_ctor_get(v_impl_7263_, 4);
lean_inc(v_r_7270_);
v___x_7271_ = lean_unsigned_to_nat(3u);
v___x_7272_ = lean_nat_mul(v___x_7271_, v_size_7265_);
v___x_7273_ = lean_nat_dec_lt(v___x_7272_, v_size_7266_);
lean_dec(v___x_7272_);
if (v___x_7273_ == 0)
{
lean_object* v___x_7274_; lean_object* v___x_7275_; lean_object* v___x_7277_; 
lean_dec(v_r_7270_);
lean_dec(v_l_7269_);
lean_dec(v_v_7268_);
lean_dec(v_k_7267_);
v___x_7274_ = lean_nat_add(v___x_7264_, v_size_7265_);
v___x_7275_ = lean_nat_add(v___x_7274_, v_size_7266_);
lean_dec(v_size_7266_);
lean_dec(v___x_7274_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_impl_7263_);
lean_ctor_set(v___x_7120_, 0, v___x_7275_);
v___x_7277_ = v___x_7120_;
goto v_reusejp_7276_;
}
else
{
lean_object* v_reuseFailAlloc_7278_; 
v_reuseFailAlloc_7278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7278_, 0, v___x_7275_);
lean_ctor_set(v_reuseFailAlloc_7278_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7278_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7278_, 3, v_l_7117_);
lean_ctor_set(v_reuseFailAlloc_7278_, 4, v_impl_7263_);
v___x_7277_ = v_reuseFailAlloc_7278_;
goto v_reusejp_7276_;
}
v_reusejp_7276_:
{
return v___x_7277_;
}
}
else
{
lean_object* v___x_7280_; uint8_t v_isShared_7281_; uint8_t v_isSharedCheck_7342_; 
v_isSharedCheck_7342_ = !lean_is_exclusive(v_impl_7263_);
if (v_isSharedCheck_7342_ == 0)
{
lean_object* v_unused_7343_; lean_object* v_unused_7344_; lean_object* v_unused_7345_; lean_object* v_unused_7346_; lean_object* v_unused_7347_; 
v_unused_7343_ = lean_ctor_get(v_impl_7263_, 4);
lean_dec(v_unused_7343_);
v_unused_7344_ = lean_ctor_get(v_impl_7263_, 3);
lean_dec(v_unused_7344_);
v_unused_7345_ = lean_ctor_get(v_impl_7263_, 2);
lean_dec(v_unused_7345_);
v_unused_7346_ = lean_ctor_get(v_impl_7263_, 1);
lean_dec(v_unused_7346_);
v_unused_7347_ = lean_ctor_get(v_impl_7263_, 0);
lean_dec(v_unused_7347_);
v___x_7280_ = v_impl_7263_;
v_isShared_7281_ = v_isSharedCheck_7342_;
goto v_resetjp_7279_;
}
else
{
lean_dec(v_impl_7263_);
v___x_7280_ = lean_box(0);
v_isShared_7281_ = v_isSharedCheck_7342_;
goto v_resetjp_7279_;
}
v_resetjp_7279_:
{
lean_object* v_size_7282_; lean_object* v_k_7283_; lean_object* v_v_7284_; lean_object* v_l_7285_; lean_object* v_r_7286_; lean_object* v_size_7287_; lean_object* v___x_7288_; lean_object* v___x_7289_; uint8_t v___x_7290_; 
v_size_7282_ = lean_ctor_get(v_l_7269_, 0);
v_k_7283_ = lean_ctor_get(v_l_7269_, 1);
v_v_7284_ = lean_ctor_get(v_l_7269_, 2);
v_l_7285_ = lean_ctor_get(v_l_7269_, 3);
v_r_7286_ = lean_ctor_get(v_l_7269_, 4);
v_size_7287_ = lean_ctor_get(v_r_7270_, 0);
v___x_7288_ = lean_unsigned_to_nat(2u);
v___x_7289_ = lean_nat_mul(v___x_7288_, v_size_7287_);
v___x_7290_ = lean_nat_dec_lt(v_size_7282_, v___x_7289_);
lean_dec(v___x_7289_);
if (v___x_7290_ == 0)
{
lean_object* v___x_7292_; uint8_t v_isShared_7293_; uint8_t v_isSharedCheck_7318_; 
lean_inc(v_r_7286_);
lean_inc(v_l_7285_);
lean_inc(v_v_7284_);
lean_inc(v_k_7283_);
v_isSharedCheck_7318_ = !lean_is_exclusive(v_l_7269_);
if (v_isSharedCheck_7318_ == 0)
{
lean_object* v_unused_7319_; lean_object* v_unused_7320_; lean_object* v_unused_7321_; lean_object* v_unused_7322_; lean_object* v_unused_7323_; 
v_unused_7319_ = lean_ctor_get(v_l_7269_, 4);
lean_dec(v_unused_7319_);
v_unused_7320_ = lean_ctor_get(v_l_7269_, 3);
lean_dec(v_unused_7320_);
v_unused_7321_ = lean_ctor_get(v_l_7269_, 2);
lean_dec(v_unused_7321_);
v_unused_7322_ = lean_ctor_get(v_l_7269_, 1);
lean_dec(v_unused_7322_);
v_unused_7323_ = lean_ctor_get(v_l_7269_, 0);
lean_dec(v_unused_7323_);
v___x_7292_ = v_l_7269_;
v_isShared_7293_ = v_isSharedCheck_7318_;
goto v_resetjp_7291_;
}
else
{
lean_dec(v_l_7269_);
v___x_7292_ = lean_box(0);
v_isShared_7293_ = v_isSharedCheck_7318_;
goto v_resetjp_7291_;
}
v_resetjp_7291_:
{
lean_object* v___x_7294_; lean_object* v___x_7295_; lean_object* v___y_7297_; lean_object* v___y_7298_; lean_object* v___y_7299_; lean_object* v___y_7308_; 
v___x_7294_ = lean_nat_add(v___x_7264_, v_size_7265_);
v___x_7295_ = lean_nat_add(v___x_7294_, v_size_7266_);
lean_dec(v_size_7266_);
if (lean_obj_tag(v_l_7285_) == 0)
{
lean_object* v_size_7316_; 
v_size_7316_ = lean_ctor_get(v_l_7285_, 0);
lean_inc(v_size_7316_);
v___y_7308_ = v_size_7316_;
goto v___jp_7307_;
}
else
{
lean_object* v___x_7317_; 
v___x_7317_ = lean_unsigned_to_nat(0u);
v___y_7308_ = v___x_7317_;
goto v___jp_7307_;
}
v___jp_7296_:
{
lean_object* v___x_7300_; lean_object* v___x_7302_; 
v___x_7300_ = lean_nat_add(v___y_7298_, v___y_7299_);
lean_dec(v___y_7299_);
lean_dec(v___y_7298_);
if (v_isShared_7293_ == 0)
{
lean_ctor_set(v___x_7292_, 4, v_r_7270_);
lean_ctor_set(v___x_7292_, 3, v_r_7286_);
lean_ctor_set(v___x_7292_, 2, v_v_7268_);
lean_ctor_set(v___x_7292_, 1, v_k_7267_);
lean_ctor_set(v___x_7292_, 0, v___x_7300_);
v___x_7302_ = v___x_7292_;
goto v_reusejp_7301_;
}
else
{
lean_object* v_reuseFailAlloc_7306_; 
v_reuseFailAlloc_7306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7306_, 0, v___x_7300_);
lean_ctor_set(v_reuseFailAlloc_7306_, 1, v_k_7267_);
lean_ctor_set(v_reuseFailAlloc_7306_, 2, v_v_7268_);
lean_ctor_set(v_reuseFailAlloc_7306_, 3, v_r_7286_);
lean_ctor_set(v_reuseFailAlloc_7306_, 4, v_r_7270_);
v___x_7302_ = v_reuseFailAlloc_7306_;
goto v_reusejp_7301_;
}
v_reusejp_7301_:
{
lean_object* v___x_7304_; 
if (v_isShared_7281_ == 0)
{
lean_ctor_set(v___x_7280_, 4, v___x_7302_);
lean_ctor_set(v___x_7280_, 3, v___y_7297_);
lean_ctor_set(v___x_7280_, 2, v_v_7284_);
lean_ctor_set(v___x_7280_, 1, v_k_7283_);
lean_ctor_set(v___x_7280_, 0, v___x_7295_);
v___x_7304_ = v___x_7280_;
goto v_reusejp_7303_;
}
else
{
lean_object* v_reuseFailAlloc_7305_; 
v_reuseFailAlloc_7305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7305_, 0, v___x_7295_);
lean_ctor_set(v_reuseFailAlloc_7305_, 1, v_k_7283_);
lean_ctor_set(v_reuseFailAlloc_7305_, 2, v_v_7284_);
lean_ctor_set(v_reuseFailAlloc_7305_, 3, v___y_7297_);
lean_ctor_set(v_reuseFailAlloc_7305_, 4, v___x_7302_);
v___x_7304_ = v_reuseFailAlloc_7305_;
goto v_reusejp_7303_;
}
v_reusejp_7303_:
{
return v___x_7304_;
}
}
}
v___jp_7307_:
{
lean_object* v___x_7309_; lean_object* v___x_7311_; 
v___x_7309_ = lean_nat_add(v___x_7294_, v___y_7308_);
lean_dec(v___y_7308_);
lean_dec(v___x_7294_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_l_7285_);
lean_ctor_set(v___x_7120_, 0, v___x_7309_);
v___x_7311_ = v___x_7120_;
goto v_reusejp_7310_;
}
else
{
lean_object* v_reuseFailAlloc_7315_; 
v_reuseFailAlloc_7315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7315_, 0, v___x_7309_);
lean_ctor_set(v_reuseFailAlloc_7315_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7315_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7315_, 3, v_l_7117_);
lean_ctor_set(v_reuseFailAlloc_7315_, 4, v_l_7285_);
v___x_7311_ = v_reuseFailAlloc_7315_;
goto v_reusejp_7310_;
}
v_reusejp_7310_:
{
lean_object* v___x_7312_; 
v___x_7312_ = lean_nat_add(v___x_7264_, v_size_7287_);
if (lean_obj_tag(v_r_7286_) == 0)
{
lean_object* v_size_7313_; 
v_size_7313_ = lean_ctor_get(v_r_7286_, 0);
lean_inc(v_size_7313_);
v___y_7297_ = v___x_7311_;
v___y_7298_ = v___x_7312_;
v___y_7299_ = v_size_7313_;
goto v___jp_7296_;
}
else
{
lean_object* v___x_7314_; 
v___x_7314_ = lean_unsigned_to_nat(0u);
v___y_7297_ = v___x_7311_;
v___y_7298_ = v___x_7312_;
v___y_7299_ = v___x_7314_;
goto v___jp_7296_;
}
}
}
}
}
else
{
lean_object* v___x_7324_; lean_object* v___x_7325_; lean_object* v___x_7326_; lean_object* v___x_7328_; 
lean_del_object(v___x_7120_);
v___x_7324_ = lean_nat_add(v___x_7264_, v_size_7265_);
v___x_7325_ = lean_nat_add(v___x_7324_, v_size_7266_);
lean_dec(v_size_7266_);
v___x_7326_ = lean_nat_add(v___x_7324_, v_size_7282_);
lean_dec(v___x_7324_);
lean_inc_ref(v_l_7117_);
if (v_isShared_7281_ == 0)
{
lean_ctor_set(v___x_7280_, 4, v_l_7269_);
lean_ctor_set(v___x_7280_, 3, v_l_7117_);
lean_ctor_set(v___x_7280_, 2, v_v_7116_);
lean_ctor_set(v___x_7280_, 1, v_k_7115_);
lean_ctor_set(v___x_7280_, 0, v___x_7326_);
v___x_7328_ = v___x_7280_;
goto v_reusejp_7327_;
}
else
{
lean_object* v_reuseFailAlloc_7341_; 
v_reuseFailAlloc_7341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7341_, 0, v___x_7326_);
lean_ctor_set(v_reuseFailAlloc_7341_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7341_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7341_, 3, v_l_7117_);
lean_ctor_set(v_reuseFailAlloc_7341_, 4, v_l_7269_);
v___x_7328_ = v_reuseFailAlloc_7341_;
goto v_reusejp_7327_;
}
v_reusejp_7327_:
{
lean_object* v___x_7330_; uint8_t v_isShared_7331_; uint8_t v_isSharedCheck_7335_; 
v_isSharedCheck_7335_ = !lean_is_exclusive(v_l_7117_);
if (v_isSharedCheck_7335_ == 0)
{
lean_object* v_unused_7336_; lean_object* v_unused_7337_; lean_object* v_unused_7338_; lean_object* v_unused_7339_; lean_object* v_unused_7340_; 
v_unused_7336_ = lean_ctor_get(v_l_7117_, 4);
lean_dec(v_unused_7336_);
v_unused_7337_ = lean_ctor_get(v_l_7117_, 3);
lean_dec(v_unused_7337_);
v_unused_7338_ = lean_ctor_get(v_l_7117_, 2);
lean_dec(v_unused_7338_);
v_unused_7339_ = lean_ctor_get(v_l_7117_, 1);
lean_dec(v_unused_7339_);
v_unused_7340_ = lean_ctor_get(v_l_7117_, 0);
lean_dec(v_unused_7340_);
v___x_7330_ = v_l_7117_;
v_isShared_7331_ = v_isSharedCheck_7335_;
goto v_resetjp_7329_;
}
else
{
lean_dec(v_l_7117_);
v___x_7330_ = lean_box(0);
v_isShared_7331_ = v_isSharedCheck_7335_;
goto v_resetjp_7329_;
}
v_resetjp_7329_:
{
lean_object* v___x_7333_; 
if (v_isShared_7331_ == 0)
{
lean_ctor_set(v___x_7330_, 4, v_r_7270_);
lean_ctor_set(v___x_7330_, 3, v___x_7328_);
lean_ctor_set(v___x_7330_, 2, v_v_7268_);
lean_ctor_set(v___x_7330_, 1, v_k_7267_);
lean_ctor_set(v___x_7330_, 0, v___x_7325_);
v___x_7333_ = v___x_7330_;
goto v_reusejp_7332_;
}
else
{
lean_object* v_reuseFailAlloc_7334_; 
v_reuseFailAlloc_7334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7334_, 0, v___x_7325_);
lean_ctor_set(v_reuseFailAlloc_7334_, 1, v_k_7267_);
lean_ctor_set(v_reuseFailAlloc_7334_, 2, v_v_7268_);
lean_ctor_set(v_reuseFailAlloc_7334_, 3, v___x_7328_);
lean_ctor_set(v_reuseFailAlloc_7334_, 4, v_r_7270_);
v___x_7333_ = v_reuseFailAlloc_7334_;
goto v_reusejp_7332_;
}
v_reusejp_7332_:
{
return v___x_7333_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7348_; 
v_l_7348_ = lean_ctor_get(v_impl_7263_, 3);
lean_inc(v_l_7348_);
if (lean_obj_tag(v_l_7348_) == 0)
{
lean_object* v_r_7349_; lean_object* v_k_7350_; lean_object* v_v_7351_; lean_object* v___x_7353_; uint8_t v_isShared_7354_; uint8_t v_isSharedCheck_7374_; 
v_r_7349_ = lean_ctor_get(v_impl_7263_, 4);
v_k_7350_ = lean_ctor_get(v_impl_7263_, 1);
v_v_7351_ = lean_ctor_get(v_impl_7263_, 2);
v_isSharedCheck_7374_ = !lean_is_exclusive(v_impl_7263_);
if (v_isSharedCheck_7374_ == 0)
{
lean_object* v_unused_7375_; lean_object* v_unused_7376_; 
v_unused_7375_ = lean_ctor_get(v_impl_7263_, 3);
lean_dec(v_unused_7375_);
v_unused_7376_ = lean_ctor_get(v_impl_7263_, 0);
lean_dec(v_unused_7376_);
v___x_7353_ = v_impl_7263_;
v_isShared_7354_ = v_isSharedCheck_7374_;
goto v_resetjp_7352_;
}
else
{
lean_inc(v_r_7349_);
lean_inc(v_v_7351_);
lean_inc(v_k_7350_);
lean_dec(v_impl_7263_);
v___x_7353_ = lean_box(0);
v_isShared_7354_ = v_isSharedCheck_7374_;
goto v_resetjp_7352_;
}
v_resetjp_7352_:
{
lean_object* v_k_7355_; lean_object* v_v_7356_; lean_object* v___x_7358_; uint8_t v_isShared_7359_; uint8_t v_isSharedCheck_7370_; 
v_k_7355_ = lean_ctor_get(v_l_7348_, 1);
v_v_7356_ = lean_ctor_get(v_l_7348_, 2);
v_isSharedCheck_7370_ = !lean_is_exclusive(v_l_7348_);
if (v_isSharedCheck_7370_ == 0)
{
lean_object* v_unused_7371_; lean_object* v_unused_7372_; lean_object* v_unused_7373_; 
v_unused_7371_ = lean_ctor_get(v_l_7348_, 4);
lean_dec(v_unused_7371_);
v_unused_7372_ = lean_ctor_get(v_l_7348_, 3);
lean_dec(v_unused_7372_);
v_unused_7373_ = lean_ctor_get(v_l_7348_, 0);
lean_dec(v_unused_7373_);
v___x_7358_ = v_l_7348_;
v_isShared_7359_ = v_isSharedCheck_7370_;
goto v_resetjp_7357_;
}
else
{
lean_inc(v_v_7356_);
lean_inc(v_k_7355_);
lean_dec(v_l_7348_);
v___x_7358_ = lean_box(0);
v_isShared_7359_ = v_isSharedCheck_7370_;
goto v_resetjp_7357_;
}
v_resetjp_7357_:
{
lean_object* v___x_7360_; lean_object* v___x_7362_; 
v___x_7360_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7349_, 2);
if (v_isShared_7359_ == 0)
{
lean_ctor_set(v___x_7358_, 4, v_r_7349_);
lean_ctor_set(v___x_7358_, 3, v_r_7349_);
lean_ctor_set(v___x_7358_, 2, v_v_7116_);
lean_ctor_set(v___x_7358_, 1, v_k_7115_);
lean_ctor_set(v___x_7358_, 0, v___x_7264_);
v___x_7362_ = v___x_7358_;
goto v_reusejp_7361_;
}
else
{
lean_object* v_reuseFailAlloc_7369_; 
v_reuseFailAlloc_7369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7369_, 0, v___x_7264_);
lean_ctor_set(v_reuseFailAlloc_7369_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7369_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7369_, 3, v_r_7349_);
lean_ctor_set(v_reuseFailAlloc_7369_, 4, v_r_7349_);
v___x_7362_ = v_reuseFailAlloc_7369_;
goto v_reusejp_7361_;
}
v_reusejp_7361_:
{
lean_object* v___x_7364_; 
lean_inc(v_r_7349_);
if (v_isShared_7354_ == 0)
{
lean_ctor_set(v___x_7353_, 3, v_r_7349_);
lean_ctor_set(v___x_7353_, 0, v___x_7264_);
v___x_7364_ = v___x_7353_;
goto v_reusejp_7363_;
}
else
{
lean_object* v_reuseFailAlloc_7368_; 
v_reuseFailAlloc_7368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7368_, 0, v___x_7264_);
lean_ctor_set(v_reuseFailAlloc_7368_, 1, v_k_7350_);
lean_ctor_set(v_reuseFailAlloc_7368_, 2, v_v_7351_);
lean_ctor_set(v_reuseFailAlloc_7368_, 3, v_r_7349_);
lean_ctor_set(v_reuseFailAlloc_7368_, 4, v_r_7349_);
v___x_7364_ = v_reuseFailAlloc_7368_;
goto v_reusejp_7363_;
}
v_reusejp_7363_:
{
lean_object* v___x_7366_; 
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v___x_7364_);
lean_ctor_set(v___x_7120_, 3, v___x_7362_);
lean_ctor_set(v___x_7120_, 2, v_v_7356_);
lean_ctor_set(v___x_7120_, 1, v_k_7355_);
lean_ctor_set(v___x_7120_, 0, v___x_7360_);
v___x_7366_ = v___x_7120_;
goto v_reusejp_7365_;
}
else
{
lean_object* v_reuseFailAlloc_7367_; 
v_reuseFailAlloc_7367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7367_, 0, v___x_7360_);
lean_ctor_set(v_reuseFailAlloc_7367_, 1, v_k_7355_);
lean_ctor_set(v_reuseFailAlloc_7367_, 2, v_v_7356_);
lean_ctor_set(v_reuseFailAlloc_7367_, 3, v___x_7362_);
lean_ctor_set(v_reuseFailAlloc_7367_, 4, v___x_7364_);
v___x_7366_ = v_reuseFailAlloc_7367_;
goto v_reusejp_7365_;
}
v_reusejp_7365_:
{
return v___x_7366_;
}
}
}
}
}
}
else
{
lean_object* v_r_7377_; 
v_r_7377_ = lean_ctor_get(v_impl_7263_, 4);
lean_inc(v_r_7377_);
if (lean_obj_tag(v_r_7377_) == 0)
{
lean_object* v_k_7378_; lean_object* v_v_7379_; lean_object* v___x_7381_; uint8_t v_isShared_7382_; uint8_t v_isSharedCheck_7390_; 
v_k_7378_ = lean_ctor_get(v_impl_7263_, 1);
v_v_7379_ = lean_ctor_get(v_impl_7263_, 2);
v_isSharedCheck_7390_ = !lean_is_exclusive(v_impl_7263_);
if (v_isSharedCheck_7390_ == 0)
{
lean_object* v_unused_7391_; lean_object* v_unused_7392_; lean_object* v_unused_7393_; 
v_unused_7391_ = lean_ctor_get(v_impl_7263_, 4);
lean_dec(v_unused_7391_);
v_unused_7392_ = lean_ctor_get(v_impl_7263_, 3);
lean_dec(v_unused_7392_);
v_unused_7393_ = lean_ctor_get(v_impl_7263_, 0);
lean_dec(v_unused_7393_);
v___x_7381_ = v_impl_7263_;
v_isShared_7382_ = v_isSharedCheck_7390_;
goto v_resetjp_7380_;
}
else
{
lean_inc(v_v_7379_);
lean_inc(v_k_7378_);
lean_dec(v_impl_7263_);
v___x_7381_ = lean_box(0);
v_isShared_7382_ = v_isSharedCheck_7390_;
goto v_resetjp_7380_;
}
v_resetjp_7380_:
{
lean_object* v___x_7383_; lean_object* v___x_7385_; 
v___x_7383_ = lean_unsigned_to_nat(3u);
if (v_isShared_7382_ == 0)
{
lean_ctor_set(v___x_7381_, 4, v_l_7348_);
lean_ctor_set(v___x_7381_, 2, v_v_7116_);
lean_ctor_set(v___x_7381_, 1, v_k_7115_);
lean_ctor_set(v___x_7381_, 0, v___x_7264_);
v___x_7385_ = v___x_7381_;
goto v_reusejp_7384_;
}
else
{
lean_object* v_reuseFailAlloc_7389_; 
v_reuseFailAlloc_7389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7389_, 0, v___x_7264_);
lean_ctor_set(v_reuseFailAlloc_7389_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7389_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7389_, 3, v_l_7348_);
lean_ctor_set(v_reuseFailAlloc_7389_, 4, v_l_7348_);
v___x_7385_ = v_reuseFailAlloc_7389_;
goto v_reusejp_7384_;
}
v_reusejp_7384_:
{
lean_object* v___x_7387_; 
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_r_7377_);
lean_ctor_set(v___x_7120_, 3, v___x_7385_);
lean_ctor_set(v___x_7120_, 2, v_v_7379_);
lean_ctor_set(v___x_7120_, 1, v_k_7378_);
lean_ctor_set(v___x_7120_, 0, v___x_7383_);
v___x_7387_ = v___x_7120_;
goto v_reusejp_7386_;
}
else
{
lean_object* v_reuseFailAlloc_7388_; 
v_reuseFailAlloc_7388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7388_, 0, v___x_7383_);
lean_ctor_set(v_reuseFailAlloc_7388_, 1, v_k_7378_);
lean_ctor_set(v_reuseFailAlloc_7388_, 2, v_v_7379_);
lean_ctor_set(v_reuseFailAlloc_7388_, 3, v___x_7385_);
lean_ctor_set(v_reuseFailAlloc_7388_, 4, v_r_7377_);
v___x_7387_ = v_reuseFailAlloc_7388_;
goto v_reusejp_7386_;
}
v_reusejp_7386_:
{
return v___x_7387_;
}
}
}
}
else
{
lean_object* v___x_7394_; lean_object* v___x_7396_; 
v___x_7394_ = lean_unsigned_to_nat(2u);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_impl_7263_);
lean_ctor_set(v___x_7120_, 3, v_r_7377_);
lean_ctor_set(v___x_7120_, 0, v___x_7394_);
v___x_7396_ = v___x_7120_;
goto v_reusejp_7395_;
}
else
{
lean_object* v_reuseFailAlloc_7397_; 
v_reuseFailAlloc_7397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7397_, 0, v___x_7394_);
lean_ctor_set(v_reuseFailAlloc_7397_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7397_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7397_, 3, v_r_7377_);
lean_ctor_set(v_reuseFailAlloc_7397_, 4, v_impl_7263_);
v___x_7396_ = v_reuseFailAlloc_7397_;
goto v_reusejp_7395_;
}
v_reusejp_7395_:
{
return v___x_7396_;
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
lean_object* v___x_7399_; lean_object* v___x_7400_; 
v___x_7399_ = lean_unsigned_to_nat(1u);
v___x_7400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7400_, 0, v___x_7399_);
lean_ctor_set(v___x_7400_, 1, v_k_7111_);
lean_ctor_set(v___x_7400_, 2, v_v_7112_);
lean_ctor_set(v___x_7400_, 3, v_t_7113_);
lean_ctor_set(v___x_7400_, 4, v_t_7113_);
return v___x_7400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7401_, lean_object* v_ps_7402_, lean_object* v_v_7403_, lean_object* v_o_7404_){
_start:
{
lean_object* v_name_7405_; lean_object* v_deps_7406_; lean_object* v_o_7407_; uint8_t v___x_7408_; 
v_name_7405_ = lean_ctor_get(v_lib_7401_, 1);
lean_inc_ref(v_name_7405_);
v_deps_7406_ = lean_ctor_get(v_lib_7401_, 2);
lean_inc_ref(v_deps_7406_);
v_o_7407_ = lean_array_push(v_o_7404_, v_lib_7401_);
v___x_7408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7405_, v_v_7403_);
if (v___x_7408_ == 0)
{
uint8_t v___x_7409_; 
v___x_7409_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7405_, v_ps_7402_);
if (v___x_7409_ == 0)
{
lean_object* v_ps_7410_; lean_object* v___y_7412_; 
lean_inc_ref(v_name_7405_);
v_ps_7410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7410_, 0, v_name_7405_);
lean_ctor_set(v_ps_7410_, 1, v_ps_7402_);
if (v___x_7408_ == 0)
{
lean_object* v___x_7426_; lean_object* v___x_7427_; 
v___x_7426_ = lean_box(0);
v___x_7427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7405_, v___x_7426_, v_v_7403_);
v___y_7412_ = v___x_7427_;
goto v___jp_7411_;
}
else
{
lean_dec_ref(v_name_7405_);
v___y_7412_ = v_v_7403_;
goto v___jp_7411_;
}
v___jp_7411_:
{
lean_object* v___x_7413_; lean_object* v___x_7414_; lean_object* v___x_7415_; uint8_t v___x_7416_; 
v___x_7413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7413_, 0, v___y_7412_);
lean_ctor_set(v___x_7413_, 1, v_o_7407_);
v___x_7414_ = lean_unsigned_to_nat(0u);
v___x_7415_ = lean_array_get_size(v_deps_7406_);
v___x_7416_ = lean_nat_dec_lt(v___x_7414_, v___x_7415_);
if (v___x_7416_ == 0)
{
lean_object* v___x_7417_; 
lean_dec_ref_known(v_ps_7410_, 2);
lean_dec_ref(v_deps_7406_);
v___x_7417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7417_, 0, v___x_7413_);
return v___x_7417_;
}
else
{
uint8_t v___x_7418_; 
v___x_7418_ = lean_nat_dec_le(v___x_7415_, v___x_7415_);
if (v___x_7418_ == 0)
{
if (v___x_7416_ == 0)
{
lean_object* v___x_7419_; 
lean_dec_ref_known(v_ps_7410_, 2);
lean_dec_ref(v_deps_7406_);
v___x_7419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7419_, 0, v___x_7413_);
return v___x_7419_;
}
else
{
size_t v___x_7420_; size_t v___x_7421_; lean_object* v___x_7422_; 
v___x_7420_ = ((size_t)0ULL);
v___x_7421_ = lean_usize_of_nat(v___x_7415_);
v___x_7422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7410_, v_deps_7406_, v___x_7420_, v___x_7421_, v___x_7413_);
lean_dec_ref(v_deps_7406_);
return v___x_7422_;
}
}
else
{
size_t v___x_7423_; size_t v___x_7424_; lean_object* v___x_7425_; 
v___x_7423_ = ((size_t)0ULL);
v___x_7424_ = lean_usize_of_nat(v___x_7415_);
v___x_7425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7410_, v_deps_7406_, v___x_7423_, v___x_7424_, v___x_7413_);
lean_dec_ref(v_deps_7406_);
return v___x_7425_;
}
}
}
}
else
{
lean_object* v___x_7428_; lean_object* v___x_7429_; 
lean_dec_ref(v_o_7407_);
lean_dec_ref(v_deps_7406_);
lean_dec(v_v_7403_);
v___x_7428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7428_, 0, v_name_7405_);
lean_ctor_set(v___x_7428_, 1, v_ps_7402_);
v___x_7429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7429_, 0, v___x_7428_);
return v___x_7429_;
}
}
else
{
lean_object* v___x_7430_; lean_object* v___x_7431_; 
lean_dec_ref(v_deps_7406_);
lean_dec_ref(v_name_7405_);
lean_dec(v_ps_7402_);
v___x_7430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7430_, 0, v_v_7403_);
lean_ctor_set(v___x_7430_, 1, v_o_7407_);
v___x_7431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7431_, 0, v___x_7430_);
return v___x_7431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7432_, lean_object* v_as_7433_, size_t v_i_7434_, size_t v_stop_7435_, lean_object* v_b_7436_){
_start:
{
uint8_t v___x_7437_; 
v___x_7437_ = lean_usize_dec_eq(v_i_7434_, v_stop_7435_);
if (v___x_7437_ == 0)
{
lean_object* v_fst_7438_; lean_object* v_snd_7439_; lean_object* v___x_7440_; lean_object* v___x_7441_; 
v_fst_7438_ = lean_ctor_get(v_b_7436_, 0);
lean_inc(v_fst_7438_);
v_snd_7439_ = lean_ctor_get(v_b_7436_, 1);
lean_inc(v_snd_7439_);
lean_dec_ref(v_b_7436_);
v___x_7440_ = lean_array_uget_borrowed(v_as_7433_, v_i_7434_);
lean_inc(v_ps_7432_);
lean_inc(v___x_7440_);
v___x_7441_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7440_, v_ps_7432_, v_fst_7438_, v_snd_7439_);
if (lean_obj_tag(v___x_7441_) == 0)
{
lean_dec(v_ps_7432_);
return v___x_7441_;
}
else
{
lean_object* v_a_7442_; size_t v___x_7443_; size_t v___x_7444_; 
v_a_7442_ = lean_ctor_get(v___x_7441_, 0);
lean_inc(v_a_7442_);
lean_dec_ref_known(v___x_7441_, 1);
v___x_7443_ = ((size_t)1ULL);
v___x_7444_ = lean_usize_add(v_i_7434_, v___x_7443_);
v_i_7434_ = v___x_7444_;
v_b_7436_ = v_a_7442_;
goto _start;
}
}
else
{
lean_object* v___x_7446_; 
lean_dec(v_ps_7432_);
v___x_7446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7446_, 0, v_b_7436_);
return v___x_7446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7447_, lean_object* v_as_7448_, lean_object* v_i_7449_, lean_object* v_stop_7450_, lean_object* v_b_7451_){
_start:
{
size_t v_i_boxed_7452_; size_t v_stop_boxed_7453_; lean_object* v_res_7454_; 
v_i_boxed_7452_ = lean_unbox_usize(v_i_7449_);
lean_dec(v_i_7449_);
v_stop_boxed_7453_ = lean_unbox_usize(v_stop_7450_);
lean_dec(v_stop_7450_);
v_res_7454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7447_, v_as_7448_, v_i_boxed_7452_, v_stop_boxed_7453_, v_b_7451_);
lean_dec_ref(v_as_7448_);
return v_res_7454_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7455_, lean_object* v_k_7456_, lean_object* v_t_7457_){
_start:
{
uint8_t v___x_7458_; 
v___x_7458_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7456_, v_t_7457_);
return v___x_7458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7459_, lean_object* v_k_7460_, lean_object* v_t_7461_){
_start:
{
uint8_t v_res_7462_; lean_object* v_r_7463_; 
v_res_7462_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7459_, v_k_7460_, v_t_7461_);
lean_dec(v_t_7461_);
lean_dec_ref(v_k_7460_);
v_r_7463_ = lean_box(v_res_7462_);
return v_r_7463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7464_, lean_object* v_k_7465_, lean_object* v_v_7466_, lean_object* v_t_7467_, lean_object* v_hl_7468_){
_start:
{
lean_object* v___x_7469_; 
v___x_7469_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7465_, v_v_7466_, v_t_7467_);
return v___x_7469_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7471_, lean_object* v_a_7472_){
_start:
{
if (lean_obj_tag(v_a_7471_) == 0)
{
lean_object* v___x_7473_; 
v___x_7473_ = l_List_reverse___redArg(v_a_7472_);
return v___x_7473_;
}
else
{
lean_object* v_head_7474_; lean_object* v_tail_7475_; lean_object* v___x_7477_; uint8_t v_isShared_7478_; uint8_t v_isSharedCheck_7485_; 
v_head_7474_ = lean_ctor_get(v_a_7471_, 0);
v_tail_7475_ = lean_ctor_get(v_a_7471_, 1);
v_isSharedCheck_7485_ = !lean_is_exclusive(v_a_7471_);
if (v_isSharedCheck_7485_ == 0)
{
v___x_7477_ = v_a_7471_;
v_isShared_7478_ = v_isSharedCheck_7485_;
goto v_resetjp_7476_;
}
else
{
lean_inc(v_tail_7475_);
lean_inc(v_head_7474_);
lean_dec(v_a_7471_);
v___x_7477_ = lean_box(0);
v_isShared_7478_ = v_isSharedCheck_7485_;
goto v_resetjp_7476_;
}
v_resetjp_7476_:
{
lean_object* v___x_7479_; lean_object* v___x_7480_; lean_object* v___x_7482_; 
v___x_7479_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7480_ = lean_string_append(v___x_7479_, v_head_7474_);
lean_dec(v_head_7474_);
if (v_isShared_7478_ == 0)
{
lean_ctor_set(v___x_7477_, 1, v_a_7472_);
lean_ctor_set(v___x_7477_, 0, v___x_7480_);
v___x_7482_ = v___x_7477_;
goto v_reusejp_7481_;
}
else
{
lean_object* v_reuseFailAlloc_7484_; 
v_reuseFailAlloc_7484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7484_, 0, v___x_7480_);
lean_ctor_set(v_reuseFailAlloc_7484_, 1, v_a_7472_);
v___x_7482_ = v_reuseFailAlloc_7484_;
goto v_reusejp_7481_;
}
v_reusejp_7481_:
{
v_a_7471_ = v_tail_7475_;
v_a_7472_ = v___x_7482_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7486_){
_start:
{
lean_object* v___x_7487_; lean_object* v___x_7488_; lean_object* v___x_7489_; lean_object* v___x_7490_; 
v___x_7487_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7488_ = lean_box(0);
v___x_7489_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7486_, v___x_7488_);
v___x_7490_ = l_String_intercalate(v___x_7487_, v___x_7489_);
return v___x_7490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object* v_as_7491_, size_t v_i_7492_, size_t v_stop_7493_, lean_object* v_b_7494_){
_start:
{
uint8_t v___x_7495_; 
v___x_7495_ = lean_usize_dec_eq(v_i_7492_, v_stop_7493_);
if (v___x_7495_ == 0)
{
lean_object* v_fst_7496_; lean_object* v_snd_7497_; lean_object* v___x_7498_; lean_object* v___x_7499_; lean_object* v___x_7500_; 
v_fst_7496_ = lean_ctor_get(v_b_7494_, 0);
lean_inc(v_fst_7496_);
v_snd_7497_ = lean_ctor_get(v_b_7494_, 1);
lean_inc(v_snd_7497_);
lean_dec_ref(v_b_7494_);
v___x_7498_ = lean_array_uget_borrowed(v_as_7491_, v_i_7492_);
v___x_7499_ = lean_box(0);
lean_inc(v___x_7498_);
v___x_7500_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7498_, v___x_7499_, v_fst_7496_, v_snd_7497_);
if (lean_obj_tag(v___x_7500_) == 0)
{
return v___x_7500_;
}
else
{
lean_object* v_a_7501_; size_t v___x_7502_; size_t v___x_7503_; 
v_a_7501_ = lean_ctor_get(v___x_7500_, 0);
lean_inc(v_a_7501_);
lean_dec_ref_known(v___x_7500_, 1);
v___x_7502_ = ((size_t)1ULL);
v___x_7503_ = lean_usize_add(v_i_7492_, v___x_7502_);
v_i_7492_ = v___x_7503_;
v_b_7494_ = v_a_7501_;
goto _start;
}
}
else
{
lean_object* v___x_7505_; 
v___x_7505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7505_, 0, v_b_7494_);
return v___x_7505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7506_, lean_object* v_i_7507_, lean_object* v_stop_7508_, lean_object* v_b_7509_){
_start:
{
size_t v_i_boxed_7510_; size_t v_stop_boxed_7511_; lean_object* v_res_7512_; 
v_i_boxed_7510_ = lean_unbox_usize(v_i_7507_);
lean_dec(v_i_7507_);
v_stop_boxed_7511_ = lean_unbox_usize(v_stop_7508_);
lean_dec(v_stop_7508_);
v_res_7512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_as_7506_, v_i_boxed_7510_, v_stop_boxed_7511_, v_b_7509_);
lean_dec_ref(v_as_7506_);
return v_res_7512_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object* v_libs_7519_, lean_object* v_a_7520_){
_start:
{
lean_object* v_snd_7523_; lean_object* v___y_7526_; lean_object* v___x_7550_; lean_object* v___x_7551_; lean_object* v___x_7552_; uint8_t v___x_7553_; 
v___x_7550_ = lean_unsigned_to_nat(0u);
v___x_7551_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7552_ = lean_array_get_size(v_libs_7519_);
v___x_7553_ = lean_nat_dec_lt(v___x_7550_, v___x_7552_);
if (v___x_7553_ == 0)
{
v_snd_7523_ = v___x_7551_;
goto v___jp_7522_;
}
else
{
lean_object* v___x_7554_; uint8_t v___x_7555_; 
v___x_7554_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__2));
v___x_7555_ = lean_nat_dec_le(v___x_7552_, v___x_7552_);
if (v___x_7555_ == 0)
{
if (v___x_7553_ == 0)
{
v_snd_7523_ = v___x_7551_;
goto v___jp_7522_;
}
else
{
size_t v___x_7556_; size_t v___x_7557_; lean_object* v___x_7558_; 
v___x_7556_ = ((size_t)0ULL);
v___x_7557_ = lean_usize_of_nat(v___x_7552_);
v___x_7558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7519_, v___x_7556_, v___x_7557_, v___x_7554_);
v___y_7526_ = v___x_7558_;
goto v___jp_7525_;
}
}
else
{
size_t v___x_7559_; size_t v___x_7560_; lean_object* v___x_7561_; 
v___x_7559_ = ((size_t)0ULL);
v___x_7560_ = lean_usize_of_nat(v___x_7552_);
v___x_7561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7519_, v___x_7559_, v___x_7560_, v___x_7554_);
v___y_7526_ = v___x_7561_;
goto v___jp_7525_;
}
}
v___jp_7522_:
{
lean_object* v___x_7524_; 
v___x_7524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7524_, 0, v_snd_7523_);
lean_ctor_set(v___x_7524_, 1, v_a_7520_);
return v___x_7524_;
}
v___jp_7525_:
{
if (lean_obj_tag(v___y_7526_) == 0)
{
lean_object* v_a_7527_; lean_object* v_log_7528_; uint8_t v_action_7529_; uint8_t v_wantsRebuild_7530_; lean_object* v_trace_7531_; lean_object* v_buildTime_7532_; lean_object* v___x_7534_; uint8_t v_isShared_7535_; uint8_t v_isSharedCheck_7547_; 
v_a_7527_ = lean_ctor_get(v___y_7526_, 0);
lean_inc(v_a_7527_);
lean_dec_ref_known(v___y_7526_, 1);
v_log_7528_ = lean_ctor_get(v_a_7520_, 0);
v_action_7529_ = lean_ctor_get_uint8(v_a_7520_, sizeof(void*)*3);
v_wantsRebuild_7530_ = lean_ctor_get_uint8(v_a_7520_, sizeof(void*)*3 + 1);
v_trace_7531_ = lean_ctor_get(v_a_7520_, 1);
v_buildTime_7532_ = lean_ctor_get(v_a_7520_, 2);
v_isSharedCheck_7547_ = !lean_is_exclusive(v_a_7520_);
if (v_isSharedCheck_7547_ == 0)
{
v___x_7534_ = v_a_7520_;
v_isShared_7535_ = v_isSharedCheck_7547_;
goto v_resetjp_7533_;
}
else
{
lean_inc(v_buildTime_7532_);
lean_inc(v_trace_7531_);
lean_inc(v_log_7528_);
lean_dec(v_a_7520_);
v___x_7534_ = lean_box(0);
v_isShared_7535_ = v_isSharedCheck_7547_;
goto v_resetjp_7533_;
}
v_resetjp_7533_:
{
lean_object* v___x_7536_; lean_object* v___x_7537_; lean_object* v___x_7538_; uint8_t v___x_7539_; lean_object* v___x_7540_; lean_object* v___x_7541_; lean_object* v___x_7542_; lean_object* v___x_7544_; 
v___x_7536_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__0));
v___x_7537_ = l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(v_a_7527_);
v___x_7538_ = lean_string_append(v___x_7536_, v___x_7537_);
lean_dec_ref(v___x_7537_);
v___x_7539_ = 3;
v___x_7540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7540_, 0, v___x_7538_);
lean_ctor_set_uint8(v___x_7540_, sizeof(void*)*1, v___x_7539_);
v___x_7541_ = lean_array_get_size(v_log_7528_);
v___x_7542_ = lean_array_push(v_log_7528_, v___x_7540_);
if (v_isShared_7535_ == 0)
{
lean_ctor_set(v___x_7534_, 0, v___x_7542_);
v___x_7544_ = v___x_7534_;
goto v_reusejp_7543_;
}
else
{
lean_object* v_reuseFailAlloc_7546_; 
v_reuseFailAlloc_7546_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7546_, 0, v___x_7542_);
lean_ctor_set(v_reuseFailAlloc_7546_, 1, v_trace_7531_);
lean_ctor_set(v_reuseFailAlloc_7546_, 2, v_buildTime_7532_);
lean_ctor_set_uint8(v_reuseFailAlloc_7546_, sizeof(void*)*3, v_action_7529_);
lean_ctor_set_uint8(v_reuseFailAlloc_7546_, sizeof(void*)*3 + 1, v_wantsRebuild_7530_);
v___x_7544_ = v_reuseFailAlloc_7546_;
goto v_reusejp_7543_;
}
v_reusejp_7543_:
{
lean_object* v___x_7545_; 
v___x_7545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7545_, 0, v___x_7541_);
lean_ctor_set(v___x_7545_, 1, v___x_7544_);
return v___x_7545_;
}
}
}
else
{
lean_object* v_a_7548_; lean_object* v_snd_7549_; 
v_a_7548_ = lean_ctor_get(v___y_7526_, 0);
lean_inc(v_a_7548_);
lean_dec_ref_known(v___y_7526_, 1);
v_snd_7549_ = lean_ctor_get(v_a_7548_, 1);
lean_inc(v_snd_7549_);
lean_dec(v_a_7548_);
v_snd_7523_ = v_snd_7549_;
goto v___jp_7522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7562_, lean_object* v_a_7563_, lean_object* v_a_7564_){
_start:
{
lean_object* v_res_7565_; 
v_res_7565_ = l_Lake_mkLinkOrder___redArg(v_libs_7562_, v_a_7563_);
lean_dec_ref(v_libs_7562_);
return v_res_7565_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object* v_libs_7566_, lean_object* v_a_7567_, lean_object* v_a_7568_, lean_object* v_a_7569_, lean_object* v_a_7570_, lean_object* v_a_7571_, lean_object* v_a_7572_){
_start:
{
lean_object* v___x_7574_; 
v___x_7574_ = l_Lake_mkLinkOrder___redArg(v_libs_7566_, v_a_7572_);
return v___x_7574_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object* v_libs_7575_, lean_object* v_a_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_){
_start:
{
lean_object* v_res_7583_; 
v_res_7583_ = l_Lake_mkLinkOrder(v_libs_7575_, v_a_7576_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_, v_a_7581_);
lean_dec_ref(v_a_7580_);
lean_dec(v_a_7579_);
lean_dec(v_a_7578_);
lean_dec(v_a_7577_);
lean_dec_ref(v_a_7576_);
lean_dec_ref(v_libs_7575_);
return v_res_7583_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object* v_objs_7584_, lean_object* v_libs_7585_, uint8_t v_linkDeps_7586_, lean_object* v_a_7587_){
_start:
{
lean_object* v_libs_7590_; lean_object* v___y_7591_; 
if (v_linkDeps_7586_ == 0)
{
lean_object* v___x_7594_; 
v___x_7594_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7590_ = v___x_7594_;
v___y_7591_ = v_a_7587_;
goto v___jp_7589_;
}
else
{
lean_object* v___x_7595_; 
v___x_7595_ = l_Lake_mkLinkOrder___redArg(v_libs_7585_, v_a_7587_);
if (lean_obj_tag(v___x_7595_) == 0)
{
lean_object* v_a_7596_; lean_object* v_a_7597_; 
v_a_7596_ = lean_ctor_get(v___x_7595_, 0);
lean_inc(v_a_7596_);
v_a_7597_ = lean_ctor_get(v___x_7595_, 1);
lean_inc(v_a_7597_);
lean_dec_ref_known(v___x_7595_, 2);
v_libs_7590_ = v_a_7596_;
v___y_7591_ = v_a_7597_;
goto v___jp_7589_;
}
else
{
lean_object* v_a_7598_; lean_object* v_a_7599_; lean_object* v___x_7601_; uint8_t v_isShared_7602_; uint8_t v_isSharedCheck_7606_; 
v_a_7598_ = lean_ctor_get(v___x_7595_, 0);
v_a_7599_ = lean_ctor_get(v___x_7595_, 1);
v_isSharedCheck_7606_ = !lean_is_exclusive(v___x_7595_);
if (v_isSharedCheck_7606_ == 0)
{
v___x_7601_ = v___x_7595_;
v_isShared_7602_ = v_isSharedCheck_7606_;
goto v_resetjp_7600_;
}
else
{
lean_inc(v_a_7599_);
lean_inc(v_a_7598_);
lean_dec(v___x_7595_);
v___x_7601_ = lean_box(0);
v_isShared_7602_ = v_isSharedCheck_7606_;
goto v_resetjp_7600_;
}
v_resetjp_7600_:
{
lean_object* v___x_7604_; 
if (v_isShared_7602_ == 0)
{
v___x_7604_ = v___x_7601_;
goto v_reusejp_7603_;
}
else
{
lean_object* v_reuseFailAlloc_7605_; 
v_reuseFailAlloc_7605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7605_, 0, v_a_7598_);
lean_ctor_set(v_reuseFailAlloc_7605_, 1, v_a_7599_);
v___x_7604_ = v_reuseFailAlloc_7605_;
goto v_reusejp_7603_;
}
v_reusejp_7603_:
{
return v___x_7604_;
}
}
}
}
v___jp_7589_:
{
lean_object* v___x_7592_; lean_object* v___x_7593_; 
v___x_7592_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7584_, v_libs_7590_);
lean_dec_ref(v_libs_7590_);
v___x_7593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7593_, 0, v___x_7592_);
lean_ctor_set(v___x_7593_, 1, v___y_7591_);
return v___x_7593_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object* v_objs_7607_, lean_object* v_libs_7608_, lean_object* v_linkDeps_7609_, lean_object* v_a_7610_, lean_object* v_a_7611_){
_start:
{
uint8_t v_linkDeps_boxed_7612_; lean_object* v_res_7613_; 
v_linkDeps_boxed_7612_ = lean_unbox(v_linkDeps_7609_);
v_res_7613_ = l_Lake_mkLinkArgs___redArg(v_objs_7607_, v_libs_7608_, v_linkDeps_boxed_7612_, v_a_7610_);
lean_dec_ref(v_libs_7608_);
lean_dec_ref(v_objs_7607_);
return v_res_7613_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object* v_objs_7614_, lean_object* v_libs_7615_, uint8_t v_linkDeps_7616_, lean_object* v_a_7617_, lean_object* v_a_7618_, lean_object* v_a_7619_, lean_object* v_a_7620_, lean_object* v_a_7621_, lean_object* v_a_7622_){
_start:
{
lean_object* v_libs_7625_; lean_object* v___y_7626_; 
if (v_linkDeps_7616_ == 0)
{
lean_object* v___x_7629_; 
v___x_7629_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7625_ = v___x_7629_;
v___y_7626_ = v_a_7622_;
goto v___jp_7624_;
}
else
{
lean_object* v___x_7630_; 
v___x_7630_ = l_Lake_mkLinkOrder___redArg(v_libs_7615_, v_a_7622_);
if (lean_obj_tag(v___x_7630_) == 0)
{
lean_object* v_a_7631_; lean_object* v_a_7632_; 
v_a_7631_ = lean_ctor_get(v___x_7630_, 0);
lean_inc(v_a_7631_);
v_a_7632_ = lean_ctor_get(v___x_7630_, 1);
lean_inc(v_a_7632_);
lean_dec_ref_known(v___x_7630_, 2);
v_libs_7625_ = v_a_7631_;
v___y_7626_ = v_a_7632_;
goto v___jp_7624_;
}
else
{
lean_object* v_a_7633_; lean_object* v_a_7634_; lean_object* v___x_7636_; uint8_t v_isShared_7637_; uint8_t v_isSharedCheck_7641_; 
v_a_7633_ = lean_ctor_get(v___x_7630_, 0);
v_a_7634_ = lean_ctor_get(v___x_7630_, 1);
v_isSharedCheck_7641_ = !lean_is_exclusive(v___x_7630_);
if (v_isSharedCheck_7641_ == 0)
{
v___x_7636_ = v___x_7630_;
v_isShared_7637_ = v_isSharedCheck_7641_;
goto v_resetjp_7635_;
}
else
{
lean_inc(v_a_7634_);
lean_inc(v_a_7633_);
lean_dec(v___x_7630_);
v___x_7636_ = lean_box(0);
v_isShared_7637_ = v_isSharedCheck_7641_;
goto v_resetjp_7635_;
}
v_resetjp_7635_:
{
lean_object* v___x_7639_; 
if (v_isShared_7637_ == 0)
{
v___x_7639_ = v___x_7636_;
goto v_reusejp_7638_;
}
else
{
lean_object* v_reuseFailAlloc_7640_; 
v_reuseFailAlloc_7640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7640_, 0, v_a_7633_);
lean_ctor_set(v_reuseFailAlloc_7640_, 1, v_a_7634_);
v___x_7639_ = v_reuseFailAlloc_7640_;
goto v_reusejp_7638_;
}
v_reusejp_7638_:
{
return v___x_7639_;
}
}
}
}
v___jp_7624_:
{
lean_object* v___x_7627_; lean_object* v___x_7628_; 
v___x_7627_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7614_, v_libs_7625_);
lean_dec_ref(v_libs_7625_);
v___x_7628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7628_, 0, v___x_7627_);
lean_ctor_set(v___x_7628_, 1, v___y_7626_);
return v___x_7628_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object* v_objs_7642_, lean_object* v_libs_7643_, lean_object* v_linkDeps_7644_, lean_object* v_a_7645_, lean_object* v_a_7646_, lean_object* v_a_7647_, lean_object* v_a_7648_, lean_object* v_a_7649_, lean_object* v_a_7650_, lean_object* v_a_7651_){
_start:
{
uint8_t v_linkDeps_boxed_7652_; lean_object* v_res_7653_; 
v_linkDeps_boxed_7652_ = lean_unbox(v_linkDeps_7644_);
v_res_7653_ = l_Lake_mkLinkArgs(v_objs_7642_, v_libs_7643_, v_linkDeps_boxed_7652_, v_a_7645_, v_a_7646_, v_a_7647_, v_a_7648_, v_a_7649_, v_a_7650_);
lean_dec_ref(v_a_7649_);
lean_dec(v_a_7648_);
lean_dec(v_a_7647_);
lean_dec(v_a_7646_);
lean_dec_ref(v_a_7645_);
lean_dec_ref(v_libs_7643_);
lean_dec_ref(v_objs_7642_);
return v_res_7653_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0(void){
_start:
{
lean_object* v___x_7654_; lean_object* v___x_7655_; lean_object* v___x_7656_; lean_object* v___x_7657_; 
v___x_7654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7655_ = lean_unsigned_to_nat(2u);
v___x_7656_ = lean_mk_empty_array_with_capacity(v___x_7655_);
v___x_7657_ = lean_array_push(v___x_7656_, v___x_7654_);
return v___x_7657_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object* v_objs_7658_, lean_object* v_libs_7659_, lean_object* v_args_7660_, uint8_t v_linkDeps_7661_, uint8_t v_sharedLean_7662_, lean_object* v_a_7663_, lean_object* v_a_7664_){
_start:
{
lean_object* v_toContext_7666_; lean_object* v_lakeEnv_7667_; lean_object* v_lean_7668_; lean_object* v_libs_7670_; lean_object* v___y_7671_; 
v_toContext_7666_ = lean_ctor_get(v_a_7663_, 1);
v_lakeEnv_7667_ = lean_ctor_get(v_toContext_7666_, 0);
v_lean_7668_ = lean_ctor_get(v_lakeEnv_7667_, 1);
if (v_linkDeps_7661_ == 0)
{
lean_object* v___x_7681_; 
v___x_7681_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7670_ = v___x_7681_;
v___y_7671_ = v_a_7664_;
goto v___jp_7669_;
}
else
{
lean_object* v___x_7682_; 
v___x_7682_ = l_Lake_mkLinkOrder___redArg(v_libs_7659_, v_a_7664_);
if (lean_obj_tag(v___x_7682_) == 0)
{
lean_object* v_a_7683_; lean_object* v_a_7684_; 
v_a_7683_ = lean_ctor_get(v___x_7682_, 0);
lean_inc(v_a_7683_);
v_a_7684_ = lean_ctor_get(v___x_7682_, 1);
lean_inc(v_a_7684_);
lean_dec_ref_known(v___x_7682_, 2);
v_libs_7670_ = v_a_7683_;
v___y_7671_ = v_a_7684_;
goto v___jp_7669_;
}
else
{
lean_object* v_a_7685_; lean_object* v_a_7686_; lean_object* v___x_7688_; uint8_t v_isShared_7689_; uint8_t v_isSharedCheck_7693_; 
v_a_7685_ = lean_ctor_get(v___x_7682_, 0);
v_a_7686_ = lean_ctor_get(v___x_7682_, 1);
v_isSharedCheck_7693_ = !lean_is_exclusive(v___x_7682_);
if (v_isSharedCheck_7693_ == 0)
{
v___x_7688_ = v___x_7682_;
v_isShared_7689_ = v_isSharedCheck_7693_;
goto v_resetjp_7687_;
}
else
{
lean_inc(v_a_7686_);
lean_inc(v_a_7685_);
lean_dec(v___x_7682_);
v___x_7688_ = lean_box(0);
v_isShared_7689_ = v_isSharedCheck_7693_;
goto v_resetjp_7687_;
}
v_resetjp_7687_:
{
lean_object* v___x_7691_; 
if (v_isShared_7689_ == 0)
{
v___x_7691_ = v___x_7688_;
goto v_reusejp_7690_;
}
else
{
lean_object* v_reuseFailAlloc_7692_; 
v_reuseFailAlloc_7692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7692_, 0, v_a_7685_);
lean_ctor_set(v_reuseFailAlloc_7692_, 1, v_a_7686_);
v___x_7691_ = v_reuseFailAlloc_7692_;
goto v_reusejp_7690_;
}
v_reusejp_7690_:
{
return v___x_7691_;
}
}
}
}
v___jp_7669_:
{
lean_object* v_leanLibDir_7672_; lean_object* v___x_7673_; lean_object* v___x_7674_; lean_object* v___x_7675_; lean_object* v___x_7676_; lean_object* v___x_7677_; lean_object* v___x_7678_; lean_object* v___x_7679_; lean_object* v___x_7680_; 
v_leanLibDir_7672_ = lean_ctor_get(v_lean_7668_, 3);
v___x_7673_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7658_, v_libs_7670_);
lean_dec_ref(v_libs_7670_);
v___x_7674_ = l_Array_append___redArg(v___x_7673_, v_args_7660_);
v___x_7675_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7672_);
v___x_7676_ = lean_array_push(v___x_7675_, v_leanLibDir_7672_);
v___x_7677_ = l_Array_append___redArg(v___x_7674_, v___x_7676_);
lean_dec_ref(v___x_7676_);
v___x_7678_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7662_, v_lean_7668_);
v___x_7679_ = l_Array_append___redArg(v___x_7677_, v___x_7678_);
lean_dec_ref(v___x_7678_);
v___x_7680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7680_, 0, v___x_7679_);
lean_ctor_set(v___x_7680_, 1, v___y_7671_);
return v___x_7680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object* v_objs_7694_, lean_object* v_libs_7695_, lean_object* v_args_7696_, lean_object* v_linkDeps_7697_, lean_object* v_sharedLean_7698_, lean_object* v_a_7699_, lean_object* v_a_7700_, lean_object* v_a_7701_){
_start:
{
uint8_t v_linkDeps_boxed_7702_; uint8_t v_sharedLean_boxed_7703_; lean_object* v_res_7704_; 
v_linkDeps_boxed_7702_ = lean_unbox(v_linkDeps_7697_);
v_sharedLean_boxed_7703_ = lean_unbox(v_sharedLean_7698_);
v_res_7704_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(v_objs_7694_, v_libs_7695_, v_args_7696_, v_linkDeps_boxed_7702_, v_sharedLean_boxed_7703_, v_a_7699_, v_a_7700_);
lean_dec_ref(v_a_7699_);
lean_dec_ref(v_args_7696_);
lean_dec_ref(v_libs_7695_);
lean_dec_ref(v_objs_7694_);
return v_res_7704_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object* v_objs_7705_, lean_object* v_libs_7706_, lean_object* v_args_7707_, uint8_t v_linkDeps_7708_, uint8_t v_sharedLean_7709_, lean_object* v_a_7710_, lean_object* v_a_7711_, lean_object* v_a_7712_, lean_object* v_a_7713_, lean_object* v_a_7714_, lean_object* v_a_7715_){
_start:
{
lean_object* v_toContext_7717_; lean_object* v_lakeEnv_7718_; lean_object* v_lean_7719_; lean_object* v_libs_7721_; lean_object* v___y_7722_; 
v_toContext_7717_ = lean_ctor_get(v_a_7714_, 1);
v_lakeEnv_7718_ = lean_ctor_get(v_toContext_7717_, 0);
v_lean_7719_ = lean_ctor_get(v_lakeEnv_7718_, 1);
if (v_linkDeps_7708_ == 0)
{
lean_object* v___x_7734_; 
v___x_7734_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7721_ = v___x_7734_;
v___y_7722_ = v_a_7715_;
goto v___jp_7720_;
}
else
{
lean_object* v___x_7735_; 
v___x_7735_ = l_Lake_mkLinkOrder___redArg(v_libs_7706_, v_a_7715_);
if (lean_obj_tag(v___x_7735_) == 0)
{
lean_object* v_a_7736_; lean_object* v_a_7737_; 
v_a_7736_ = lean_ctor_get(v___x_7735_, 0);
lean_inc(v_a_7736_);
v_a_7737_ = lean_ctor_get(v___x_7735_, 1);
lean_inc(v_a_7737_);
lean_dec_ref_known(v___x_7735_, 2);
v_libs_7721_ = v_a_7736_;
v___y_7722_ = v_a_7737_;
goto v___jp_7720_;
}
else
{
lean_object* v_a_7738_; lean_object* v_a_7739_; lean_object* v___x_7741_; uint8_t v_isShared_7742_; uint8_t v_isSharedCheck_7746_; 
v_a_7738_ = lean_ctor_get(v___x_7735_, 0);
v_a_7739_ = lean_ctor_get(v___x_7735_, 1);
v_isSharedCheck_7746_ = !lean_is_exclusive(v___x_7735_);
if (v_isSharedCheck_7746_ == 0)
{
v___x_7741_ = v___x_7735_;
v_isShared_7742_ = v_isSharedCheck_7746_;
goto v_resetjp_7740_;
}
else
{
lean_inc(v_a_7739_);
lean_inc(v_a_7738_);
lean_dec(v___x_7735_);
v___x_7741_ = lean_box(0);
v_isShared_7742_ = v_isSharedCheck_7746_;
goto v_resetjp_7740_;
}
v_resetjp_7740_:
{
lean_object* v___x_7744_; 
if (v_isShared_7742_ == 0)
{
v___x_7744_ = v___x_7741_;
goto v_reusejp_7743_;
}
else
{
lean_object* v_reuseFailAlloc_7745_; 
v_reuseFailAlloc_7745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7745_, 0, v_a_7738_);
lean_ctor_set(v_reuseFailAlloc_7745_, 1, v_a_7739_);
v___x_7744_ = v_reuseFailAlloc_7745_;
goto v_reusejp_7743_;
}
v_reusejp_7743_:
{
return v___x_7744_;
}
}
}
}
v___jp_7720_:
{
lean_object* v_leanLibDir_7723_; lean_object* v___x_7724_; lean_object* v___x_7725_; lean_object* v___x_7726_; lean_object* v___x_7727_; lean_object* v___x_7728_; lean_object* v___x_7729_; lean_object* v___x_7730_; lean_object* v___x_7731_; lean_object* v___x_7732_; lean_object* v___x_7733_; 
v_leanLibDir_7723_ = lean_ctor_get(v_lean_7719_, 3);
v___x_7724_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7705_, v_libs_7721_);
lean_dec_ref(v_libs_7721_);
v___x_7725_ = l_Array_append___redArg(v___x_7724_, v_args_7707_);
v___x_7726_ = lean_unsigned_to_nat(2u);
v___x_7727_ = lean_mk_empty_array_with_capacity(v___x_7726_);
lean_dec_ref(v___x_7727_);
v___x_7728_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7723_);
v___x_7729_ = lean_array_push(v___x_7728_, v_leanLibDir_7723_);
v___x_7730_ = l_Array_append___redArg(v___x_7725_, v___x_7729_);
lean_dec_ref(v___x_7729_);
v___x_7731_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7709_, v_lean_7719_);
v___x_7732_ = l_Array_append___redArg(v___x_7730_, v___x_7731_);
lean_dec_ref(v___x_7731_);
v___x_7733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7733_, 0, v___x_7732_);
lean_ctor_set(v___x_7733_, 1, v___y_7722_);
return v___x_7733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object* v_objs_7747_, lean_object* v_libs_7748_, lean_object* v_args_7749_, lean_object* v_linkDeps_7750_, lean_object* v_sharedLean_7751_, lean_object* v_a_7752_, lean_object* v_a_7753_, lean_object* v_a_7754_, lean_object* v_a_7755_, lean_object* v_a_7756_, lean_object* v_a_7757_, lean_object* v_a_7758_){
_start:
{
uint8_t v_linkDeps_boxed_7759_; uint8_t v_sharedLean_boxed_7760_; lean_object* v_res_7761_; 
v_linkDeps_boxed_7759_ = lean_unbox(v_linkDeps_7750_);
v_sharedLean_boxed_7760_ = lean_unbox(v_sharedLean_7751_);
v_res_7761_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(v_objs_7747_, v_libs_7748_, v_args_7749_, v_linkDeps_boxed_7759_, v_sharedLean_boxed_7760_, v_a_7752_, v_a_7753_, v_a_7754_, v_a_7755_, v_a_7756_, v_a_7757_);
lean_dec_ref(v_a_7756_);
lean_dec(v_a_7755_);
lean_dec(v_a_7754_);
lean_dec(v_a_7753_);
lean_dec_ref(v_a_7752_);
lean_dec_ref(v_args_7749_);
lean_dec_ref(v_libs_7748_);
lean_dec_ref(v_objs_7747_);
return v_res_7761_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object* v_linkObjs_7762_, lean_object* v_args_7763_, lean_object* v_libFile_7764_, lean_object* v_linker_7765_, uint8_t v_linkDeps_7766_, lean_object* v_linkLibs_7767_, lean_object* v___y_7768_, lean_object* v___y_7769_, lean_object* v___y_7770_, lean_object* v___y_7771_, lean_object* v___y_7772_, lean_object* v___y_7773_){
_start:
{
lean_object* v_libs_7776_; lean_object* v___y_7777_; 
if (v_linkDeps_7766_ == 0)
{
lean_object* v___x_7814_; 
v___x_7814_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7776_ = v___x_7814_;
v___y_7777_ = v___y_7773_;
goto v___jp_7775_;
}
else
{
lean_object* v___x_7815_; 
v___x_7815_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_7767_, v___y_7773_);
if (lean_obj_tag(v___x_7815_) == 0)
{
lean_object* v_a_7816_; lean_object* v_a_7817_; 
v_a_7816_ = lean_ctor_get(v___x_7815_, 0);
lean_inc(v_a_7816_);
v_a_7817_ = lean_ctor_get(v___x_7815_, 1);
lean_inc(v_a_7817_);
lean_dec_ref_known(v___x_7815_, 2);
v_libs_7776_ = v_a_7816_;
v___y_7777_ = v_a_7817_;
goto v___jp_7775_;
}
else
{
lean_object* v_a_7818_; lean_object* v_a_7819_; lean_object* v___x_7821_; uint8_t v_isShared_7822_; uint8_t v_isSharedCheck_7826_; 
lean_dec_ref(v_linker_7765_);
lean_dec_ref(v_libFile_7764_);
v_a_7818_ = lean_ctor_get(v___x_7815_, 0);
v_a_7819_ = lean_ctor_get(v___x_7815_, 1);
v_isSharedCheck_7826_ = !lean_is_exclusive(v___x_7815_);
if (v_isSharedCheck_7826_ == 0)
{
v___x_7821_ = v___x_7815_;
v_isShared_7822_ = v_isSharedCheck_7826_;
goto v_resetjp_7820_;
}
else
{
lean_inc(v_a_7819_);
lean_inc(v_a_7818_);
lean_dec(v___x_7815_);
v___x_7821_ = lean_box(0);
v_isShared_7822_ = v_isSharedCheck_7826_;
goto v_resetjp_7820_;
}
v_resetjp_7820_:
{
lean_object* v___x_7824_; 
if (v_isShared_7822_ == 0)
{
v___x_7824_ = v___x_7821_;
goto v_reusejp_7823_;
}
else
{
lean_object* v_reuseFailAlloc_7825_; 
v_reuseFailAlloc_7825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7825_, 0, v_a_7818_);
lean_ctor_set(v_reuseFailAlloc_7825_, 1, v_a_7819_);
v___x_7824_ = v_reuseFailAlloc_7825_;
goto v_reusejp_7823_;
}
v_reusejp_7823_:
{
return v___x_7824_;
}
}
}
}
v___jp_7775_:
{
lean_object* v_log_7778_; uint8_t v_action_7779_; uint8_t v_wantsRebuild_7780_; lean_object* v_trace_7781_; lean_object* v_buildTime_7782_; lean_object* v___x_7784_; uint8_t v_isShared_7785_; uint8_t v_isSharedCheck_7813_; 
v_log_7778_ = lean_ctor_get(v___y_7777_, 0);
v_action_7779_ = lean_ctor_get_uint8(v___y_7777_, sizeof(void*)*3);
v_wantsRebuild_7780_ = lean_ctor_get_uint8(v___y_7777_, sizeof(void*)*3 + 1);
v_trace_7781_ = lean_ctor_get(v___y_7777_, 1);
v_buildTime_7782_ = lean_ctor_get(v___y_7777_, 2);
v_isSharedCheck_7813_ = !lean_is_exclusive(v___y_7777_);
if (v_isSharedCheck_7813_ == 0)
{
v___x_7784_ = v___y_7777_;
v_isShared_7785_ = v_isSharedCheck_7813_;
goto v_resetjp_7783_;
}
else
{
lean_inc(v_buildTime_7782_);
lean_inc(v_trace_7781_);
lean_inc(v_log_7778_);
lean_dec(v___y_7777_);
v___x_7784_ = lean_box(0);
v_isShared_7785_ = v_isSharedCheck_7813_;
goto v_resetjp_7783_;
}
v_resetjp_7783_:
{
lean_object* v___x_7786_; lean_object* v___x_7787_; lean_object* v___x_7788_; 
v___x_7786_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_7762_, v_libs_7776_);
lean_dec_ref(v_libs_7776_);
v___x_7787_ = l_Array_append___redArg(v___x_7786_, v_args_7763_);
v___x_7788_ = l_Lake_compileSharedLib(v_libFile_7764_, v___x_7787_, v_linker_7765_, v_log_7778_);
lean_dec_ref(v___x_7787_);
if (lean_obj_tag(v___x_7788_) == 0)
{
lean_object* v_a_7789_; lean_object* v_a_7790_; lean_object* v___x_7792_; uint8_t v_isShared_7793_; uint8_t v_isSharedCheck_7800_; 
v_a_7789_ = lean_ctor_get(v___x_7788_, 0);
v_a_7790_ = lean_ctor_get(v___x_7788_, 1);
v_isSharedCheck_7800_ = !lean_is_exclusive(v___x_7788_);
if (v_isSharedCheck_7800_ == 0)
{
v___x_7792_ = v___x_7788_;
v_isShared_7793_ = v_isSharedCheck_7800_;
goto v_resetjp_7791_;
}
else
{
lean_inc(v_a_7790_);
lean_inc(v_a_7789_);
lean_dec(v___x_7788_);
v___x_7792_ = lean_box(0);
v_isShared_7793_ = v_isSharedCheck_7800_;
goto v_resetjp_7791_;
}
v_resetjp_7791_:
{
lean_object* v___x_7795_; 
if (v_isShared_7785_ == 0)
{
lean_ctor_set(v___x_7784_, 0, v_a_7790_);
v___x_7795_ = v___x_7784_;
goto v_reusejp_7794_;
}
else
{
lean_object* v_reuseFailAlloc_7799_; 
v_reuseFailAlloc_7799_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7799_, 0, v_a_7790_);
lean_ctor_set(v_reuseFailAlloc_7799_, 1, v_trace_7781_);
lean_ctor_set(v_reuseFailAlloc_7799_, 2, v_buildTime_7782_);
lean_ctor_set_uint8(v_reuseFailAlloc_7799_, sizeof(void*)*3, v_action_7779_);
lean_ctor_set_uint8(v_reuseFailAlloc_7799_, sizeof(void*)*3 + 1, v_wantsRebuild_7780_);
v___x_7795_ = v_reuseFailAlloc_7799_;
goto v_reusejp_7794_;
}
v_reusejp_7794_:
{
lean_object* v___x_7797_; 
if (v_isShared_7793_ == 0)
{
lean_ctor_set(v___x_7792_, 1, v___x_7795_);
v___x_7797_ = v___x_7792_;
goto v_reusejp_7796_;
}
else
{
lean_object* v_reuseFailAlloc_7798_; 
v_reuseFailAlloc_7798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7798_, 0, v_a_7789_);
lean_ctor_set(v_reuseFailAlloc_7798_, 1, v___x_7795_);
v___x_7797_ = v_reuseFailAlloc_7798_;
goto v_reusejp_7796_;
}
v_reusejp_7796_:
{
return v___x_7797_;
}
}
}
}
else
{
lean_object* v_a_7801_; lean_object* v_a_7802_; lean_object* v___x_7804_; uint8_t v_isShared_7805_; uint8_t v_isSharedCheck_7812_; 
v_a_7801_ = lean_ctor_get(v___x_7788_, 0);
v_a_7802_ = lean_ctor_get(v___x_7788_, 1);
v_isSharedCheck_7812_ = !lean_is_exclusive(v___x_7788_);
if (v_isSharedCheck_7812_ == 0)
{
v___x_7804_ = v___x_7788_;
v_isShared_7805_ = v_isSharedCheck_7812_;
goto v_resetjp_7803_;
}
else
{
lean_inc(v_a_7802_);
lean_inc(v_a_7801_);
lean_dec(v___x_7788_);
v___x_7804_ = lean_box(0);
v_isShared_7805_ = v_isSharedCheck_7812_;
goto v_resetjp_7803_;
}
v_resetjp_7803_:
{
lean_object* v___x_7807_; 
if (v_isShared_7785_ == 0)
{
lean_ctor_set(v___x_7784_, 0, v_a_7802_);
v___x_7807_ = v___x_7784_;
goto v_reusejp_7806_;
}
else
{
lean_object* v_reuseFailAlloc_7811_; 
v_reuseFailAlloc_7811_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7811_, 0, v_a_7802_);
lean_ctor_set(v_reuseFailAlloc_7811_, 1, v_trace_7781_);
lean_ctor_set(v_reuseFailAlloc_7811_, 2, v_buildTime_7782_);
lean_ctor_set_uint8(v_reuseFailAlloc_7811_, sizeof(void*)*3, v_action_7779_);
lean_ctor_set_uint8(v_reuseFailAlloc_7811_, sizeof(void*)*3 + 1, v_wantsRebuild_7780_);
v___x_7807_ = v_reuseFailAlloc_7811_;
goto v_reusejp_7806_;
}
v_reusejp_7806_:
{
lean_object* v___x_7809_; 
if (v_isShared_7805_ == 0)
{
lean_ctor_set(v___x_7804_, 1, v___x_7807_);
v___x_7809_ = v___x_7804_;
goto v_reusejp_7808_;
}
else
{
lean_object* v_reuseFailAlloc_7810_; 
v_reuseFailAlloc_7810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7810_, 0, v_a_7801_);
lean_ctor_set(v_reuseFailAlloc_7810_, 1, v___x_7807_);
v___x_7809_ = v_reuseFailAlloc_7810_;
goto v_reusejp_7808_;
}
v_reusejp_7808_:
{
return v___x_7809_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_7827_, lean_object* v_args_7828_, lean_object* v_libFile_7829_, lean_object* v_linker_7830_, lean_object* v_linkDeps_7831_, lean_object* v_linkLibs_7832_, lean_object* v___y_7833_, lean_object* v___y_7834_, lean_object* v___y_7835_, lean_object* v___y_7836_, lean_object* v___y_7837_, lean_object* v___y_7838_, lean_object* v___y_7839_){
_start:
{
uint8_t v_linkDeps_boxed_7840_; lean_object* v_res_7841_; 
v_linkDeps_boxed_7840_ = lean_unbox(v_linkDeps_7831_);
v_res_7841_ = l_Lake_buildSharedLibSync___lam__0(v_linkObjs_7827_, v_args_7828_, v_libFile_7829_, v_linker_7830_, v_linkDeps_boxed_7840_, v_linkLibs_7832_, v___y_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_);
lean_dec_ref(v___y_7837_);
lean_dec(v___y_7836_);
lean_dec(v___y_7835_);
lean_dec(v___y_7834_);
lean_dec_ref(v___y_7833_);
lean_dec_ref(v_linkLibs_7832_);
lean_dec_ref(v_args_7828_);
lean_dec_ref(v_linkObjs_7827_);
return v_res_7841_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object* v_libName_7842_, lean_object* v_libFile_7843_, lean_object* v_linkObjs_7844_, lean_object* v_linkLibs_7845_, lean_object* v_args_7846_, lean_object* v_linker_7847_, uint8_t v_plugin_7848_, uint8_t v_linkDeps_7849_, lean_object* v_a_7850_, lean_object* v_a_7851_, lean_object* v_a_7852_, lean_object* v_a_7853_, lean_object* v_a_7854_, lean_object* v_a_7855_){
_start:
{
lean_object* v_log_7857_; uint8_t v_action_7858_; uint8_t v_wantsRebuild_7859_; lean_object* v_trace_7860_; lean_object* v_buildTime_7861_; lean_object* v___x_7863_; uint8_t v_isShared_7864_; uint8_t v_isSharedCheck_7897_; 
v_log_7857_ = lean_ctor_get(v_a_7855_, 0);
v_action_7858_ = lean_ctor_get_uint8(v_a_7855_, sizeof(void*)*3);
v_wantsRebuild_7859_ = lean_ctor_get_uint8(v_a_7855_, sizeof(void*)*3 + 1);
v_trace_7860_ = lean_ctor_get(v_a_7855_, 1);
v_buildTime_7861_ = lean_ctor_get(v_a_7855_, 2);
v_isSharedCheck_7897_ = !lean_is_exclusive(v_a_7855_);
if (v_isSharedCheck_7897_ == 0)
{
v___x_7863_ = v_a_7855_;
v_isShared_7864_ = v_isSharedCheck_7897_;
goto v_resetjp_7862_;
}
else
{
lean_inc(v_buildTime_7861_);
lean_inc(v_trace_7860_);
lean_inc(v_log_7857_);
lean_dec(v_a_7855_);
v___x_7863_ = lean_box(0);
v_isShared_7864_ = v_isSharedCheck_7897_;
goto v_resetjp_7862_;
}
v_resetjp_7862_:
{
lean_object* v___x_7865_; lean_object* v___f_7866_; lean_object* v___x_7867_; lean_object* v___x_7868_; lean_object* v___x_7870_; 
v___x_7865_ = lean_box(v_linkDeps_7849_);
lean_inc_ref(v_linkLibs_7845_);
lean_inc_ref(v_libFile_7843_);
v___f_7866_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7866_, 0, v_linkObjs_7844_);
lean_closure_set(v___f_7866_, 1, v_args_7846_);
lean_closure_set(v___f_7866_, 2, v_libFile_7843_);
lean_closure_set(v___f_7866_, 3, v_linker_7847_);
lean_closure_set(v___f_7866_, 4, v___x_7865_);
lean_closure_set(v___f_7866_, 5, v_linkLibs_7845_);
v___x_7867_ = l_Lake_platformTrace;
v___x_7868_ = l_Lake_BuildTrace_mix(v_trace_7860_, v___x_7867_);
if (v_isShared_7864_ == 0)
{
lean_ctor_set(v___x_7863_, 1, v___x_7868_);
v___x_7870_ = v___x_7863_;
goto v_reusejp_7869_;
}
else
{
lean_object* v_reuseFailAlloc_7896_; 
v_reuseFailAlloc_7896_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7896_, 0, v_log_7857_);
lean_ctor_set(v_reuseFailAlloc_7896_, 1, v___x_7868_);
lean_ctor_set(v_reuseFailAlloc_7896_, 2, v_buildTime_7861_);
lean_ctor_set_uint8(v_reuseFailAlloc_7896_, sizeof(void*)*3, v_action_7858_);
lean_ctor_set_uint8(v_reuseFailAlloc_7896_, sizeof(void*)*3 + 1, v_wantsRebuild_7859_);
v___x_7870_ = v_reuseFailAlloc_7896_;
goto v_reusejp_7869_;
}
v_reusejp_7869_:
{
uint8_t v___x_7871_; lean_object* v___x_7872_; uint8_t v___x_7873_; lean_object* v___x_7874_; 
v___x_7871_ = 0;
v___x_7872_ = l_Lake_sharedLibExt;
v___x_7873_ = 1;
v___x_7874_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7843_, v___f_7866_, v___x_7871_, v___x_7872_, v___x_7873_, v___x_7871_, v___x_7871_, v_a_7850_, v_a_7851_, v_a_7852_, v_a_7853_, v_a_7854_, v___x_7870_);
if (lean_obj_tag(v___x_7874_) == 0)
{
lean_object* v_a_7875_; lean_object* v_a_7876_; lean_object* v___x_7878_; uint8_t v_isShared_7879_; uint8_t v_isSharedCheck_7886_; 
v_a_7875_ = lean_ctor_get(v___x_7874_, 0);
v_a_7876_ = lean_ctor_get(v___x_7874_, 1);
v_isSharedCheck_7886_ = !lean_is_exclusive(v___x_7874_);
if (v_isSharedCheck_7886_ == 0)
{
v___x_7878_ = v___x_7874_;
v_isShared_7879_ = v_isSharedCheck_7886_;
goto v_resetjp_7877_;
}
else
{
lean_inc(v_a_7876_);
lean_inc(v_a_7875_);
lean_dec(v___x_7874_);
v___x_7878_ = lean_box(0);
v_isShared_7879_ = v_isSharedCheck_7886_;
goto v_resetjp_7877_;
}
v_resetjp_7877_:
{
lean_object* v_path_7880_; lean_object* v___x_7881_; lean_object* v___x_7882_; lean_object* v___x_7884_; 
v_path_7880_ = lean_ctor_get(v_a_7875_, 1);
lean_inc_ref(v_path_7880_);
lean_dec(v_a_7875_);
v___x_7881_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7882_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_7882_, 0, v_path_7880_);
lean_ctor_set(v___x_7882_, 1, v_libName_7842_);
lean_ctor_set(v___x_7882_, 2, v_linkLibs_7845_);
lean_ctor_set(v___x_7882_, 3, v___x_7881_);
lean_ctor_set_uint8(v___x_7882_, sizeof(void*)*4, v_plugin_7848_);
if (v_isShared_7879_ == 0)
{
lean_ctor_set(v___x_7878_, 0, v___x_7882_);
v___x_7884_ = v___x_7878_;
goto v_reusejp_7883_;
}
else
{
lean_object* v_reuseFailAlloc_7885_; 
v_reuseFailAlloc_7885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7885_, 0, v___x_7882_);
lean_ctor_set(v_reuseFailAlloc_7885_, 1, v_a_7876_);
v___x_7884_ = v_reuseFailAlloc_7885_;
goto v_reusejp_7883_;
}
v_reusejp_7883_:
{
return v___x_7884_;
}
}
}
else
{
lean_object* v_a_7887_; lean_object* v_a_7888_; lean_object* v___x_7890_; uint8_t v_isShared_7891_; uint8_t v_isSharedCheck_7895_; 
lean_dec_ref(v_linkLibs_7845_);
lean_dec_ref(v_libName_7842_);
v_a_7887_ = lean_ctor_get(v___x_7874_, 0);
v_a_7888_ = lean_ctor_get(v___x_7874_, 1);
v_isSharedCheck_7895_ = !lean_is_exclusive(v___x_7874_);
if (v_isSharedCheck_7895_ == 0)
{
v___x_7890_ = v___x_7874_;
v_isShared_7891_ = v_isSharedCheck_7895_;
goto v_resetjp_7889_;
}
else
{
lean_inc(v_a_7888_);
lean_inc(v_a_7887_);
lean_dec(v___x_7874_);
v___x_7890_ = lean_box(0);
v_isShared_7891_ = v_isSharedCheck_7895_;
goto v_resetjp_7889_;
}
v_resetjp_7889_:
{
lean_object* v___x_7893_; 
if (v_isShared_7891_ == 0)
{
v___x_7893_ = v___x_7890_;
goto v_reusejp_7892_;
}
else
{
lean_object* v_reuseFailAlloc_7894_; 
v_reuseFailAlloc_7894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7894_, 0, v_a_7887_);
lean_ctor_set(v_reuseFailAlloc_7894_, 1, v_a_7888_);
v___x_7893_ = v_reuseFailAlloc_7894_;
goto v_reusejp_7892_;
}
v_reusejp_7892_:
{
return v___x_7893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object* v_libName_7898_, lean_object* v_libFile_7899_, lean_object* v_linkObjs_7900_, lean_object* v_linkLibs_7901_, lean_object* v_args_7902_, lean_object* v_linker_7903_, lean_object* v_plugin_7904_, lean_object* v_linkDeps_7905_, lean_object* v_a_7906_, lean_object* v_a_7907_, lean_object* v_a_7908_, lean_object* v_a_7909_, lean_object* v_a_7910_, lean_object* v_a_7911_, lean_object* v_a_7912_){
_start:
{
uint8_t v_plugin_boxed_7913_; uint8_t v_linkDeps_boxed_7914_; lean_object* v_res_7915_; 
v_plugin_boxed_7913_ = lean_unbox(v_plugin_7904_);
v_linkDeps_boxed_7914_ = lean_unbox(v_linkDeps_7905_);
v_res_7915_ = l_Lake_buildSharedLibSync(v_libName_7898_, v_libFile_7899_, v_linkObjs_7900_, v_linkLibs_7901_, v_args_7902_, v_linker_7903_, v_plugin_boxed_7913_, v_linkDeps_boxed_7914_, v_a_7906_, v_a_7907_, v_a_7908_, v_a_7909_, v_a_7910_, v_a_7911_);
lean_dec_ref(v_a_7910_);
lean_dec(v_a_7909_);
lean_dec(v_a_7908_);
lean_dec(v_a_7907_);
return v_res_7915_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_extraDepTrace_7916_, lean_object* v_traceArgs_7917_, lean_object* v_weakArgs_7918_, lean_object* v_libName_7919_, lean_object* v_libFile_7920_, lean_object* v_objs_7921_, lean_object* v_linker_7922_, uint8_t v_plugin_7923_, uint8_t v_linkDeps_7924_, lean_object* v_libs_7925_, lean_object* v___y_7926_, lean_object* v___y_7927_, lean_object* v___y_7928_, lean_object* v___y_7929_, lean_object* v___y_7930_, lean_object* v___y_7931_){
_start:
{
lean_object* v___x_7933_; 
lean_inc_ref(v___y_7930_);
lean_inc(v___y_7929_);
lean_inc(v___y_7928_);
lean_inc(v___y_7927_);
lean_inc_ref(v___y_7926_);
v___x_7933_ = lean_apply_7(v_extraDepTrace_7916_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_, lean_box(0));
if (lean_obj_tag(v___x_7933_) == 0)
{
lean_object* v_a_7934_; lean_object* v_a_7935_; lean_object* v_log_7936_; uint8_t v_action_7937_; uint8_t v_wantsRebuild_7938_; lean_object* v_trace_7939_; lean_object* v_buildTime_7940_; lean_object* v___x_7942_; uint8_t v_isShared_7943_; uint8_t v_isSharedCheck_7973_; 
v_a_7934_ = lean_ctor_get(v___x_7933_, 1);
lean_inc(v_a_7934_);
v_a_7935_ = lean_ctor_get(v___x_7933_, 0);
lean_inc(v_a_7935_);
lean_dec_ref_known(v___x_7933_, 2);
v_log_7936_ = lean_ctor_get(v_a_7934_, 0);
v_action_7937_ = lean_ctor_get_uint8(v_a_7934_, sizeof(void*)*3);
v_wantsRebuild_7938_ = lean_ctor_get_uint8(v_a_7934_, sizeof(void*)*3 + 1);
v_trace_7939_ = lean_ctor_get(v_a_7934_, 1);
v_buildTime_7940_ = lean_ctor_get(v_a_7934_, 2);
v_isSharedCheck_7973_ = !lean_is_exclusive(v_a_7934_);
if (v_isSharedCheck_7973_ == 0)
{
v___x_7942_ = v_a_7934_;
v_isShared_7943_ = v_isSharedCheck_7973_;
goto v_resetjp_7941_;
}
else
{
lean_inc(v_buildTime_7940_);
lean_inc(v_trace_7939_);
lean_inc(v_log_7936_);
lean_dec(v_a_7934_);
v___x_7942_ = lean_box(0);
v_isShared_7943_ = v_isSharedCheck_7973_;
goto v_resetjp_7941_;
}
v_resetjp_7941_:
{
lean_object* v___x_7944_; uint64_t v___y_7946_; uint64_t v___x_7962_; lean_object* v___x_7963_; lean_object* v___x_7964_; uint8_t v___x_7965_; 
v___x_7944_ = l_Lake_BuildTrace_mix(v_trace_7939_, v_a_7935_);
v___x_7962_ = l_Lake_Hash_nil;
v___x_7963_ = lean_unsigned_to_nat(0u);
v___x_7964_ = lean_array_get_size(v_traceArgs_7917_);
v___x_7965_ = lean_nat_dec_lt(v___x_7963_, v___x_7964_);
if (v___x_7965_ == 0)
{
v___y_7946_ = v___x_7962_;
goto v___jp_7945_;
}
else
{
uint8_t v___x_7966_; 
v___x_7966_ = lean_nat_dec_le(v___x_7964_, v___x_7964_);
if (v___x_7966_ == 0)
{
if (v___x_7965_ == 0)
{
v___y_7946_ = v___x_7962_;
goto v___jp_7945_;
}
else
{
size_t v___x_7967_; size_t v___x_7968_; uint64_t v___x_7969_; 
v___x_7967_ = ((size_t)0ULL);
v___x_7968_ = lean_usize_of_nat(v___x_7964_);
v___x_7969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7917_, v___x_7967_, v___x_7968_, v___x_7962_);
v___y_7946_ = v___x_7969_;
goto v___jp_7945_;
}
}
else
{
size_t v___x_7970_; size_t v___x_7971_; uint64_t v___x_7972_; 
v___x_7970_ = ((size_t)0ULL);
v___x_7971_ = lean_usize_of_nat(v___x_7964_);
v___x_7972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7917_, v___x_7970_, v___x_7971_, v___x_7962_);
v___y_7946_ = v___x_7972_;
goto v___jp_7945_;
}
}
v___jp_7945_:
{
lean_object* v___x_7947_; lean_object* v___x_7948_; lean_object* v___x_7949_; lean_object* v___x_7950_; lean_object* v___x_7951_; lean_object* v___x_7952_; lean_object* v___x_7953_; lean_object* v___x_7954_; lean_object* v___x_7955_; lean_object* v___x_7956_; lean_object* v___x_7958_; 
v___x_7947_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7948_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_7917_);
v___x_7949_ = lean_array_to_list(v_traceArgs_7917_);
v___x_7950_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7949_);
lean_dec(v___x_7949_);
v___x_7951_ = lean_string_append(v___x_7948_, v___x_7950_);
lean_dec_ref(v___x_7950_);
v___x_7952_ = lean_string_append(v___x_7947_, v___x_7951_);
lean_dec_ref(v___x_7951_);
v___x_7953_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7954_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7955_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7955_, 0, v___x_7952_);
lean_ctor_set(v___x_7955_, 1, v___x_7953_);
lean_ctor_set(v___x_7955_, 2, v___x_7954_);
lean_ctor_set_uint64(v___x_7955_, sizeof(void*)*3, v___y_7946_);
v___x_7956_ = l_Lake_BuildTrace_mix(v___x_7944_, v___x_7955_);
if (v_isShared_7943_ == 0)
{
lean_ctor_set(v___x_7942_, 1, v___x_7956_);
v___x_7958_ = v___x_7942_;
goto v_reusejp_7957_;
}
else
{
lean_object* v_reuseFailAlloc_7961_; 
v_reuseFailAlloc_7961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7961_, 0, v_log_7936_);
lean_ctor_set(v_reuseFailAlloc_7961_, 1, v___x_7956_);
lean_ctor_set(v_reuseFailAlloc_7961_, 2, v_buildTime_7940_);
lean_ctor_set_uint8(v_reuseFailAlloc_7961_, sizeof(void*)*3, v_action_7937_);
lean_ctor_set_uint8(v_reuseFailAlloc_7961_, sizeof(void*)*3 + 1, v_wantsRebuild_7938_);
v___x_7958_ = v_reuseFailAlloc_7961_;
goto v_reusejp_7957_;
}
v_reusejp_7957_:
{
lean_object* v___x_7959_; lean_object* v___x_7960_; 
v___x_7959_ = l_Array_append___redArg(v_weakArgs_7918_, v_traceArgs_7917_);
lean_dec_ref(v_traceArgs_7917_);
v___x_7960_ = l_Lake_buildSharedLibSync(v_libName_7919_, v_libFile_7920_, v_objs_7921_, v_libs_7925_, v___x_7959_, v_linker_7922_, v_plugin_7923_, v_linkDeps_7924_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___x_7958_);
return v___x_7960_;
}
}
}
}
else
{
lean_object* v_a_7974_; lean_object* v_a_7975_; lean_object* v___x_7977_; uint8_t v_isShared_7978_; uint8_t v_isSharedCheck_7982_; 
lean_dec_ref(v___y_7926_);
lean_dec_ref(v_libs_7925_);
lean_dec_ref(v_linker_7922_);
lean_dec_ref(v_objs_7921_);
lean_dec_ref(v_libFile_7920_);
lean_dec_ref(v_libName_7919_);
lean_dec_ref(v_weakArgs_7918_);
lean_dec_ref(v_traceArgs_7917_);
v_a_7974_ = lean_ctor_get(v___x_7933_, 0);
v_a_7975_ = lean_ctor_get(v___x_7933_, 1);
v_isSharedCheck_7982_ = !lean_is_exclusive(v___x_7933_);
if (v_isSharedCheck_7982_ == 0)
{
v___x_7977_ = v___x_7933_;
v_isShared_7978_ = v_isSharedCheck_7982_;
goto v_resetjp_7976_;
}
else
{
lean_inc(v_a_7975_);
lean_inc(v_a_7974_);
lean_dec(v___x_7933_);
v___x_7977_ = lean_box(0);
v_isShared_7978_ = v_isSharedCheck_7982_;
goto v_resetjp_7976_;
}
v_resetjp_7976_:
{
lean_object* v___x_7980_; 
if (v_isShared_7978_ == 0)
{
v___x_7980_ = v___x_7977_;
goto v_reusejp_7979_;
}
else
{
lean_object* v_reuseFailAlloc_7981_; 
v_reuseFailAlloc_7981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7981_, 0, v_a_7974_);
lean_ctor_set(v_reuseFailAlloc_7981_, 1, v_a_7975_);
v___x_7980_ = v_reuseFailAlloc_7981_;
goto v_reusejp_7979_;
}
v_reusejp_7979_:
{
return v___x_7980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object** _args){
lean_object* v_extraDepTrace_7983_ = _args[0];
lean_object* v_traceArgs_7984_ = _args[1];
lean_object* v_weakArgs_7985_ = _args[2];
lean_object* v_libName_7986_ = _args[3];
lean_object* v_libFile_7987_ = _args[4];
lean_object* v_objs_7988_ = _args[5];
lean_object* v_linker_7989_ = _args[6];
lean_object* v_plugin_7990_ = _args[7];
lean_object* v_linkDeps_7991_ = _args[8];
lean_object* v_libs_7992_ = _args[9];
lean_object* v___y_7993_ = _args[10];
lean_object* v___y_7994_ = _args[11];
lean_object* v___y_7995_ = _args[12];
lean_object* v___y_7996_ = _args[13];
lean_object* v___y_7997_ = _args[14];
lean_object* v___y_7998_ = _args[15];
lean_object* v___y_7999_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8000_; uint8_t v_linkDeps_boxed_8001_; lean_object* v_res_8002_; 
v_plugin_boxed_8000_ = lean_unbox(v_plugin_7990_);
v_linkDeps_boxed_8001_ = lean_unbox(v_linkDeps_7991_);
v_res_8002_ = l_Lake_buildSharedLib___lam__0(v_extraDepTrace_7983_, v_traceArgs_7984_, v_weakArgs_7985_, v_libName_7986_, v_libFile_7987_, v_objs_7988_, v_linker_7989_, v_plugin_boxed_8000_, v_linkDeps_boxed_8001_, v_libs_7992_, v___y_7993_, v___y_7994_, v___y_7995_, v___y_7996_, v___y_7997_, v___y_7998_);
lean_dec_ref(v___y_7997_);
lean_dec(v___y_7996_);
lean_dec(v___y_7995_);
lean_dec(v___y_7994_);
return v_res_8002_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object* v_extraDepTrace_8004_, lean_object* v_traceArgs_8005_, lean_object* v_weakArgs_8006_, lean_object* v_libName_8007_, lean_object* v_libFile_8008_, lean_object* v_linker_8009_, uint8_t v_plugin_8010_, uint8_t v_linkDeps_8011_, lean_object* v_linkLibs_8012_, lean_object* v___x_8013_, lean_object* v_objs_8014_, lean_object* v___y_8015_, lean_object* v___y_8016_, lean_object* v___y_8017_, lean_object* v___y_8018_, lean_object* v___y_8019_, lean_object* v___y_8020_){
_start:
{
lean_object* v_trace_8022_; lean_object* v___x_8023_; lean_object* v___x_8024_; lean_object* v___f_8025_; lean_object* v___x_8026_; lean_object* v___x_8027_; lean_object* v___x_8028_; uint8_t v___x_8029_; lean_object* v___x_8030_; lean_object* v___x_8031_; 
v_trace_8022_ = lean_ctor_get(v___y_8020_, 1);
v___x_8023_ = lean_box(v_plugin_8010_);
v___x_8024_ = lean_box(v_linkDeps_8011_);
v___f_8025_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 17, 9);
lean_closure_set(v___f_8025_, 0, v_extraDepTrace_8004_);
lean_closure_set(v___f_8025_, 1, v_traceArgs_8005_);
lean_closure_set(v___f_8025_, 2, v_weakArgs_8006_);
lean_closure_set(v___f_8025_, 3, v_libName_8007_);
lean_closure_set(v___f_8025_, 4, v_libFile_8008_);
lean_closure_set(v___f_8025_, 5, v_objs_8014_);
lean_closure_set(v___f_8025_, 6, v_linker_8009_);
lean_closure_set(v___f_8025_, 7, v___x_8023_);
lean_closure_set(v___f_8025_, 8, v___x_8024_);
v___x_8026_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8027_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8012_, v___x_8026_);
v___x_8028_ = lean_unsigned_to_nat(0u);
v___x_8029_ = 0;
v___x_8030_ = l_Lake_Job_mapM___redArg(v___x_8013_, v___x_8027_, v___f_8025_, v___x_8028_, v___x_8029_, v___y_8015_, v___y_8016_, v___y_8017_, v___y_8018_, v___y_8019_, v_trace_8022_);
v___x_8031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8031_, 0, v___x_8030_);
lean_ctor_set(v___x_8031_, 1, v___y_8020_);
return v___x_8031_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8032_ = _args[0];
lean_object* v_traceArgs_8033_ = _args[1];
lean_object* v_weakArgs_8034_ = _args[2];
lean_object* v_libName_8035_ = _args[3];
lean_object* v_libFile_8036_ = _args[4];
lean_object* v_linker_8037_ = _args[5];
lean_object* v_plugin_8038_ = _args[6];
lean_object* v_linkDeps_8039_ = _args[7];
lean_object* v_linkLibs_8040_ = _args[8];
lean_object* v___x_8041_ = _args[9];
lean_object* v_objs_8042_ = _args[10];
lean_object* v___y_8043_ = _args[11];
lean_object* v___y_8044_ = _args[12];
lean_object* v___y_8045_ = _args[13];
lean_object* v___y_8046_ = _args[14];
lean_object* v___y_8047_ = _args[15];
lean_object* v___y_8048_ = _args[16];
lean_object* v___y_8049_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8050_; uint8_t v_linkDeps_boxed_8051_; lean_object* v_res_8052_; 
v_plugin_boxed_8050_ = lean_unbox(v_plugin_8038_);
v_linkDeps_boxed_8051_ = lean_unbox(v_linkDeps_8039_);
v_res_8052_ = l_Lake_buildSharedLib___lam__1(v_extraDepTrace_8032_, v_traceArgs_8033_, v_weakArgs_8034_, v_libName_8035_, v_libFile_8036_, v_linker_8037_, v_plugin_boxed_8050_, v_linkDeps_boxed_8051_, v_linkLibs_8040_, v___x_8041_, v_objs_8042_, v___y_8043_, v___y_8044_, v___y_8045_, v___y_8046_, v___y_8047_, v___y_8048_);
lean_dec_ref(v___y_8047_);
lean_dec(v___y_8046_);
lean_dec(v___y_8045_);
lean_dec(v___y_8044_);
lean_dec_ref(v_linkLibs_8040_);
return v_res_8052_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_8054_, lean_object* v_libFile_8055_, lean_object* v_linkObjs_8056_, lean_object* v_linkLibs_8057_, lean_object* v_weakArgs_8058_, lean_object* v_traceArgs_8059_, lean_object* v_linker_8060_, lean_object* v_extraDepTrace_8061_, uint8_t v_plugin_8062_, uint8_t v_linkDeps_8063_, lean_object* v_a_8064_, lean_object* v_a_8065_, lean_object* v_a_8066_, lean_object* v_a_8067_, lean_object* v_a_8068_, lean_object* v_a_8069_){
_start:
{
lean_object* v___x_8071_; lean_object* v___x_8072_; lean_object* v___x_8073_; lean_object* v___f_8074_; lean_object* v___x_8075_; lean_object* v___x_8076_; lean_object* v___x_8077_; uint8_t v___x_8078_; lean_object* v___x_8079_; 
v___x_8071_ = l_Lake_instDataKindDynlib;
v___x_8072_ = lean_box(v_plugin_8062_);
v___x_8073_ = lean_box(v_linkDeps_8063_);
v___f_8074_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 18, 10);
lean_closure_set(v___f_8074_, 0, v_extraDepTrace_8061_);
lean_closure_set(v___f_8074_, 1, v_traceArgs_8059_);
lean_closure_set(v___f_8074_, 2, v_weakArgs_8058_);
lean_closure_set(v___f_8074_, 3, v_libName_8054_);
lean_closure_set(v___f_8074_, 4, v_libFile_8055_);
lean_closure_set(v___f_8074_, 5, v_linker_8060_);
lean_closure_set(v___f_8074_, 6, v___x_8072_);
lean_closure_set(v___f_8074_, 7, v___x_8073_);
lean_closure_set(v___f_8074_, 8, v_linkLibs_8057_);
lean_closure_set(v___f_8074_, 9, v___x_8071_);
v___x_8075_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8076_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8056_, v___x_8075_);
v___x_8077_ = lean_unsigned_to_nat(0u);
v___x_8078_ = 1;
v___x_8079_ = l_Lake_Job_bindM___redArg(v___x_8071_, v___x_8076_, v___f_8074_, v___x_8077_, v___x_8078_, v_a_8064_, v_a_8065_, v_a_8066_, v_a_8067_, v_a_8068_, v_a_8069_);
return v___x_8079_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_8080_ = _args[0];
lean_object* v_libFile_8081_ = _args[1];
lean_object* v_linkObjs_8082_ = _args[2];
lean_object* v_linkLibs_8083_ = _args[3];
lean_object* v_weakArgs_8084_ = _args[4];
lean_object* v_traceArgs_8085_ = _args[5];
lean_object* v_linker_8086_ = _args[6];
lean_object* v_extraDepTrace_8087_ = _args[7];
lean_object* v_plugin_8088_ = _args[8];
lean_object* v_linkDeps_8089_ = _args[9];
lean_object* v_a_8090_ = _args[10];
lean_object* v_a_8091_ = _args[11];
lean_object* v_a_8092_ = _args[12];
lean_object* v_a_8093_ = _args[13];
lean_object* v_a_8094_ = _args[14];
lean_object* v_a_8095_ = _args[15];
lean_object* v_a_8096_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8097_; uint8_t v_linkDeps_boxed_8098_; lean_object* v_res_8099_; 
v_plugin_boxed_8097_ = lean_unbox(v_plugin_8088_);
v_linkDeps_boxed_8098_ = lean_unbox(v_linkDeps_8089_);
v_res_8099_ = l_Lake_buildSharedLib(v_libName_8080_, v_libFile_8081_, v_linkObjs_8082_, v_linkLibs_8083_, v_weakArgs_8084_, v_traceArgs_8085_, v_linker_8086_, v_extraDepTrace_8087_, v_plugin_boxed_8097_, v_linkDeps_boxed_8098_, v_a_8090_, v_a_8091_, v_a_8092_, v_a_8093_, v_a_8094_, v_a_8095_);
lean_dec_ref(v_a_8095_);
lean_dec_ref(v_a_8094_);
lean_dec(v_a_8093_);
lean_dec(v_a_8092_);
lean_dec(v_a_8091_);
lean_dec_ref(v_linkObjs_8082_);
return v_res_8099_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object* v_linkObjs_8100_, lean_object* v_args_8101_, uint8_t v___x_8102_, lean_object* v_libFile_8103_, uint8_t v_linkDeps_8104_, lean_object* v_linkLibs_8105_, lean_object* v___y_8106_, lean_object* v___y_8107_, lean_object* v___y_8108_, lean_object* v___y_8109_, lean_object* v___y_8110_, lean_object* v___y_8111_){
_start:
{
lean_object* v_toContext_8113_; lean_object* v_lakeEnv_8114_; lean_object* v_lean_8115_; lean_object* v_libs_8117_; lean_object* v___y_8118_; 
v_toContext_8113_ = lean_ctor_get(v___y_8110_, 1);
v_lakeEnv_8114_ = lean_ctor_get(v_toContext_8113_, 0);
v_lean_8115_ = lean_ctor_get(v_lakeEnv_8114_, 1);
if (v_linkDeps_8104_ == 0)
{
lean_object* v___x_8164_; 
v___x_8164_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_8117_ = v___x_8164_;
v___y_8118_ = v___y_8111_;
goto v___jp_8116_;
}
else
{
lean_object* v___x_8165_; 
v___x_8165_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8105_, v___y_8111_);
if (lean_obj_tag(v___x_8165_) == 0)
{
lean_object* v_a_8166_; lean_object* v_a_8167_; 
v_a_8166_ = lean_ctor_get(v___x_8165_, 0);
lean_inc(v_a_8166_);
v_a_8167_ = lean_ctor_get(v___x_8165_, 1);
lean_inc(v_a_8167_);
lean_dec_ref_known(v___x_8165_, 2);
v_libs_8117_ = v_a_8166_;
v___y_8118_ = v_a_8167_;
goto v___jp_8116_;
}
else
{
lean_object* v_a_8168_; lean_object* v_a_8169_; lean_object* v___x_8171_; uint8_t v_isShared_8172_; uint8_t v_isSharedCheck_8176_; 
lean_dec_ref(v_libFile_8103_);
v_a_8168_ = lean_ctor_get(v___x_8165_, 0);
v_a_8169_ = lean_ctor_get(v___x_8165_, 1);
v_isSharedCheck_8176_ = !lean_is_exclusive(v___x_8165_);
if (v_isSharedCheck_8176_ == 0)
{
v___x_8171_ = v___x_8165_;
v_isShared_8172_ = v_isSharedCheck_8176_;
goto v_resetjp_8170_;
}
else
{
lean_inc(v_a_8169_);
lean_inc(v_a_8168_);
lean_dec(v___x_8165_);
v___x_8171_ = lean_box(0);
v_isShared_8172_ = v_isSharedCheck_8176_;
goto v_resetjp_8170_;
}
v_resetjp_8170_:
{
lean_object* v___x_8174_; 
if (v_isShared_8172_ == 0)
{
v___x_8174_ = v___x_8171_;
goto v_reusejp_8173_;
}
else
{
lean_object* v_reuseFailAlloc_8175_; 
v_reuseFailAlloc_8175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8175_, 0, v_a_8168_);
lean_ctor_set(v_reuseFailAlloc_8175_, 1, v_a_8169_);
v___x_8174_ = v_reuseFailAlloc_8175_;
goto v_reusejp_8173_;
}
v_reusejp_8173_:
{
return v___x_8174_;
}
}
}
}
v___jp_8116_:
{
lean_object* v_leanLibDir_8119_; lean_object* v_cc_8120_; lean_object* v_log_8121_; uint8_t v_action_8122_; uint8_t v_wantsRebuild_8123_; lean_object* v_trace_8124_; lean_object* v_buildTime_8125_; lean_object* v___x_8127_; uint8_t v_isShared_8128_; uint8_t v_isSharedCheck_8163_; 
v_leanLibDir_8119_ = lean_ctor_get(v_lean_8115_, 3);
v_cc_8120_ = lean_ctor_get(v_lean_8115_, 14);
v_log_8121_ = lean_ctor_get(v___y_8118_, 0);
v_action_8122_ = lean_ctor_get_uint8(v___y_8118_, sizeof(void*)*3);
v_wantsRebuild_8123_ = lean_ctor_get_uint8(v___y_8118_, sizeof(void*)*3 + 1);
v_trace_8124_ = lean_ctor_get(v___y_8118_, 1);
v_buildTime_8125_ = lean_ctor_get(v___y_8118_, 2);
v_isSharedCheck_8163_ = !lean_is_exclusive(v___y_8118_);
if (v_isSharedCheck_8163_ == 0)
{
v___x_8127_ = v___y_8118_;
v_isShared_8128_ = v_isSharedCheck_8163_;
goto v_resetjp_8126_;
}
else
{
lean_inc(v_buildTime_8125_);
lean_inc(v_trace_8124_);
lean_inc(v_log_8121_);
lean_dec(v___y_8118_);
v___x_8127_ = lean_box(0);
v_isShared_8128_ = v_isSharedCheck_8163_;
goto v_resetjp_8126_;
}
v_resetjp_8126_:
{
lean_object* v___x_8129_; lean_object* v___x_8130_; lean_object* v___x_8131_; lean_object* v___x_8132_; lean_object* v___x_8133_; lean_object* v___x_8134_; lean_object* v___x_8135_; lean_object* v___x_8136_; lean_object* v___x_8137_; lean_object* v___x_8138_; 
v___x_8129_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8100_, v_libs_8117_);
lean_dec_ref(v_libs_8117_);
v___x_8130_ = l_Array_append___redArg(v___x_8129_, v_args_8101_);
v___x_8131_ = lean_unsigned_to_nat(2u);
v___x_8132_ = lean_mk_empty_array_with_capacity(v___x_8131_);
lean_dec_ref(v___x_8132_);
v___x_8133_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8119_);
v___x_8134_ = lean_array_push(v___x_8133_, v_leanLibDir_8119_);
v___x_8135_ = l_Array_append___redArg(v___x_8130_, v___x_8134_);
lean_dec_ref(v___x_8134_);
v___x_8136_ = l_Lake_LeanInstall_ccLinkFlags(v___x_8102_, v_lean_8115_);
v___x_8137_ = l_Array_append___redArg(v___x_8135_, v___x_8136_);
lean_dec_ref(v___x_8136_);
lean_inc_ref(v_cc_8120_);
v___x_8138_ = l_Lake_compileSharedLib(v_libFile_8103_, v___x_8137_, v_cc_8120_, v_log_8121_);
lean_dec_ref(v___x_8137_);
if (lean_obj_tag(v___x_8138_) == 0)
{
lean_object* v_a_8139_; lean_object* v_a_8140_; lean_object* v___x_8142_; uint8_t v_isShared_8143_; uint8_t v_isSharedCheck_8150_; 
v_a_8139_ = lean_ctor_get(v___x_8138_, 0);
v_a_8140_ = lean_ctor_get(v___x_8138_, 1);
v_isSharedCheck_8150_ = !lean_is_exclusive(v___x_8138_);
if (v_isSharedCheck_8150_ == 0)
{
v___x_8142_ = v___x_8138_;
v_isShared_8143_ = v_isSharedCheck_8150_;
goto v_resetjp_8141_;
}
else
{
lean_inc(v_a_8140_);
lean_inc(v_a_8139_);
lean_dec(v___x_8138_);
v___x_8142_ = lean_box(0);
v_isShared_8143_ = v_isSharedCheck_8150_;
goto v_resetjp_8141_;
}
v_resetjp_8141_:
{
lean_object* v___x_8145_; 
if (v_isShared_8128_ == 0)
{
lean_ctor_set(v___x_8127_, 0, v_a_8140_);
v___x_8145_ = v___x_8127_;
goto v_reusejp_8144_;
}
else
{
lean_object* v_reuseFailAlloc_8149_; 
v_reuseFailAlloc_8149_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8149_, 0, v_a_8140_);
lean_ctor_set(v_reuseFailAlloc_8149_, 1, v_trace_8124_);
lean_ctor_set(v_reuseFailAlloc_8149_, 2, v_buildTime_8125_);
lean_ctor_set_uint8(v_reuseFailAlloc_8149_, sizeof(void*)*3, v_action_8122_);
lean_ctor_set_uint8(v_reuseFailAlloc_8149_, sizeof(void*)*3 + 1, v_wantsRebuild_8123_);
v___x_8145_ = v_reuseFailAlloc_8149_;
goto v_reusejp_8144_;
}
v_reusejp_8144_:
{
lean_object* v___x_8147_; 
if (v_isShared_8143_ == 0)
{
lean_ctor_set(v___x_8142_, 1, v___x_8145_);
v___x_8147_ = v___x_8142_;
goto v_reusejp_8146_;
}
else
{
lean_object* v_reuseFailAlloc_8148_; 
v_reuseFailAlloc_8148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8148_, 0, v_a_8139_);
lean_ctor_set(v_reuseFailAlloc_8148_, 1, v___x_8145_);
v___x_8147_ = v_reuseFailAlloc_8148_;
goto v_reusejp_8146_;
}
v_reusejp_8146_:
{
return v___x_8147_;
}
}
}
}
else
{
lean_object* v_a_8151_; lean_object* v_a_8152_; lean_object* v___x_8154_; uint8_t v_isShared_8155_; uint8_t v_isSharedCheck_8162_; 
v_a_8151_ = lean_ctor_get(v___x_8138_, 0);
v_a_8152_ = lean_ctor_get(v___x_8138_, 1);
v_isSharedCheck_8162_ = !lean_is_exclusive(v___x_8138_);
if (v_isSharedCheck_8162_ == 0)
{
v___x_8154_ = v___x_8138_;
v_isShared_8155_ = v_isSharedCheck_8162_;
goto v_resetjp_8153_;
}
else
{
lean_inc(v_a_8152_);
lean_inc(v_a_8151_);
lean_dec(v___x_8138_);
v___x_8154_ = lean_box(0);
v_isShared_8155_ = v_isSharedCheck_8162_;
goto v_resetjp_8153_;
}
v_resetjp_8153_:
{
lean_object* v___x_8157_; 
if (v_isShared_8128_ == 0)
{
lean_ctor_set(v___x_8127_, 0, v_a_8152_);
v___x_8157_ = v___x_8127_;
goto v_reusejp_8156_;
}
else
{
lean_object* v_reuseFailAlloc_8161_; 
v_reuseFailAlloc_8161_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8161_, 0, v_a_8152_);
lean_ctor_set(v_reuseFailAlloc_8161_, 1, v_trace_8124_);
lean_ctor_set(v_reuseFailAlloc_8161_, 2, v_buildTime_8125_);
lean_ctor_set_uint8(v_reuseFailAlloc_8161_, sizeof(void*)*3, v_action_8122_);
lean_ctor_set_uint8(v_reuseFailAlloc_8161_, sizeof(void*)*3 + 1, v_wantsRebuild_8123_);
v___x_8157_ = v_reuseFailAlloc_8161_;
goto v_reusejp_8156_;
}
v_reusejp_8156_:
{
lean_object* v___x_8159_; 
if (v_isShared_8155_ == 0)
{
lean_ctor_set(v___x_8154_, 1, v___x_8157_);
v___x_8159_ = v___x_8154_;
goto v_reusejp_8158_;
}
else
{
lean_object* v_reuseFailAlloc_8160_; 
v_reuseFailAlloc_8160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8160_, 0, v_a_8151_);
lean_ctor_set(v_reuseFailAlloc_8160_, 1, v___x_8157_);
v___x_8159_ = v_reuseFailAlloc_8160_;
goto v_reusejp_8158_;
}
v_reusejp_8158_:
{
return v___x_8159_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_8177_, lean_object* v_args_8178_, lean_object* v___x_8179_, lean_object* v_libFile_8180_, lean_object* v_linkDeps_8181_, lean_object* v_linkLibs_8182_, lean_object* v___y_8183_, lean_object* v___y_8184_, lean_object* v___y_8185_, lean_object* v___y_8186_, lean_object* v___y_8187_, lean_object* v___y_8188_, lean_object* v___y_8189_){
_start:
{
uint8_t v___x_34592__boxed_8190_; uint8_t v_linkDeps_boxed_8191_; lean_object* v_res_8192_; 
v___x_34592__boxed_8190_ = lean_unbox(v___x_8179_);
v_linkDeps_boxed_8191_ = lean_unbox(v_linkDeps_8181_);
v_res_8192_ = l_Lake_buildLeanSharedLibSync___lam__0(v_linkObjs_8177_, v_args_8178_, v___x_34592__boxed_8190_, v_libFile_8180_, v_linkDeps_boxed_8191_, v_linkLibs_8182_, v___y_8183_, v___y_8184_, v___y_8185_, v___y_8186_, v___y_8187_, v___y_8188_);
lean_dec_ref(v___y_8187_);
lean_dec(v___y_8186_);
lean_dec(v___y_8185_);
lean_dec(v___y_8184_);
lean_dec_ref(v___y_8183_);
lean_dec_ref(v_linkLibs_8182_);
lean_dec_ref(v_args_8178_);
lean_dec_ref(v_linkObjs_8177_);
return v_res_8192_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object* v_libName_8193_, lean_object* v_libFile_8194_, lean_object* v_linkObjs_8195_, lean_object* v_linkLibs_8196_, lean_object* v_args_8197_, uint8_t v_plugin_8198_, uint8_t v_linkDeps_8199_, lean_object* v_a_8200_, lean_object* v_a_8201_, lean_object* v_a_8202_, lean_object* v_a_8203_, lean_object* v_a_8204_, lean_object* v_a_8205_){
_start:
{
lean_object* v_log_8207_; uint8_t v_action_8208_; uint8_t v_wantsRebuild_8209_; lean_object* v_trace_8210_; lean_object* v_buildTime_8211_; lean_object* v___x_8213_; uint8_t v_isShared_8214_; uint8_t v_isSharedCheck_8250_; 
v_log_8207_ = lean_ctor_get(v_a_8205_, 0);
v_action_8208_ = lean_ctor_get_uint8(v_a_8205_, sizeof(void*)*3);
v_wantsRebuild_8209_ = lean_ctor_get_uint8(v_a_8205_, sizeof(void*)*3 + 1);
v_trace_8210_ = lean_ctor_get(v_a_8205_, 1);
v_buildTime_8211_ = lean_ctor_get(v_a_8205_, 2);
v_isSharedCheck_8250_ = !lean_is_exclusive(v_a_8205_);
if (v_isSharedCheck_8250_ == 0)
{
v___x_8213_ = v_a_8205_;
v_isShared_8214_ = v_isSharedCheck_8250_;
goto v_resetjp_8212_;
}
else
{
lean_inc(v_buildTime_8211_);
lean_inc(v_trace_8210_);
lean_inc(v_log_8207_);
lean_dec(v_a_8205_);
v___x_8213_ = lean_box(0);
v_isShared_8214_ = v_isSharedCheck_8250_;
goto v_resetjp_8212_;
}
v_resetjp_8212_:
{
lean_object* v_leanTrace_8215_; lean_object* v___x_8216_; lean_object* v___x_8217_; lean_object* v___x_8218_; lean_object* v___x_8220_; 
v_leanTrace_8215_ = lean_ctor_get(v_a_8204_, 2);
lean_inc_ref(v_leanTrace_8215_);
v___x_8216_ = l_Lake_BuildTrace_mix(v_trace_8210_, v_leanTrace_8215_);
v___x_8217_ = l_Lake_platformTrace;
v___x_8218_ = l_Lake_BuildTrace_mix(v___x_8216_, v___x_8217_);
if (v_isShared_8214_ == 0)
{
lean_ctor_set(v___x_8213_, 1, v___x_8218_);
v___x_8220_ = v___x_8213_;
goto v_reusejp_8219_;
}
else
{
lean_object* v_reuseFailAlloc_8249_; 
v_reuseFailAlloc_8249_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8249_, 0, v_log_8207_);
lean_ctor_set(v_reuseFailAlloc_8249_, 1, v___x_8218_);
lean_ctor_set(v_reuseFailAlloc_8249_, 2, v_buildTime_8211_);
lean_ctor_set_uint8(v_reuseFailAlloc_8249_, sizeof(void*)*3, v_action_8208_);
lean_ctor_set_uint8(v_reuseFailAlloc_8249_, sizeof(void*)*3 + 1, v_wantsRebuild_8209_);
v___x_8220_ = v_reuseFailAlloc_8249_;
goto v_reusejp_8219_;
}
v_reusejp_8219_:
{
uint8_t v___x_8221_; lean_object* v___x_8222_; lean_object* v___x_8223_; lean_object* v___f_8224_; uint8_t v___x_8225_; lean_object* v___x_8226_; lean_object* v___x_8227_; 
v___x_8221_ = 1;
v___x_8222_ = lean_box(v___x_8221_);
v___x_8223_ = lean_box(v_linkDeps_8199_);
lean_inc_ref(v_linkLibs_8196_);
lean_inc_ref(v_libFile_8194_);
v___f_8224_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8224_, 0, v_linkObjs_8195_);
lean_closure_set(v___f_8224_, 1, v_args_8197_);
lean_closure_set(v___f_8224_, 2, v___x_8222_);
lean_closure_set(v___f_8224_, 3, v_libFile_8194_);
lean_closure_set(v___f_8224_, 4, v___x_8223_);
lean_closure_set(v___f_8224_, 5, v_linkLibs_8196_);
v___x_8225_ = 0;
v___x_8226_ = l_Lake_sharedLibExt;
v___x_8227_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8194_, v___f_8224_, v___x_8225_, v___x_8226_, v___x_8221_, v___x_8225_, v___x_8225_, v_a_8200_, v_a_8201_, v_a_8202_, v_a_8203_, v_a_8204_, v___x_8220_);
if (lean_obj_tag(v___x_8227_) == 0)
{
lean_object* v_a_8228_; lean_object* v_a_8229_; lean_object* v___x_8231_; uint8_t v_isShared_8232_; uint8_t v_isSharedCheck_8239_; 
v_a_8228_ = lean_ctor_get(v___x_8227_, 0);
v_a_8229_ = lean_ctor_get(v___x_8227_, 1);
v_isSharedCheck_8239_ = !lean_is_exclusive(v___x_8227_);
if (v_isSharedCheck_8239_ == 0)
{
v___x_8231_ = v___x_8227_;
v_isShared_8232_ = v_isSharedCheck_8239_;
goto v_resetjp_8230_;
}
else
{
lean_inc(v_a_8229_);
lean_inc(v_a_8228_);
lean_dec(v___x_8227_);
v___x_8231_ = lean_box(0);
v_isShared_8232_ = v_isSharedCheck_8239_;
goto v_resetjp_8230_;
}
v_resetjp_8230_:
{
lean_object* v_path_8233_; lean_object* v___x_8234_; lean_object* v___x_8235_; lean_object* v___x_8237_; 
v_path_8233_ = lean_ctor_get(v_a_8228_, 1);
lean_inc_ref(v_path_8233_);
lean_dec(v_a_8228_);
v___x_8234_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_8235_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8235_, 0, v_path_8233_);
lean_ctor_set(v___x_8235_, 1, v_libName_8193_);
lean_ctor_set(v___x_8235_, 2, v_linkLibs_8196_);
lean_ctor_set(v___x_8235_, 3, v___x_8234_);
lean_ctor_set_uint8(v___x_8235_, sizeof(void*)*4, v_plugin_8198_);
if (v_isShared_8232_ == 0)
{
lean_ctor_set(v___x_8231_, 0, v___x_8235_);
v___x_8237_ = v___x_8231_;
goto v_reusejp_8236_;
}
else
{
lean_object* v_reuseFailAlloc_8238_; 
v_reuseFailAlloc_8238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8238_, 0, v___x_8235_);
lean_ctor_set(v_reuseFailAlloc_8238_, 1, v_a_8229_);
v___x_8237_ = v_reuseFailAlloc_8238_;
goto v_reusejp_8236_;
}
v_reusejp_8236_:
{
return v___x_8237_;
}
}
}
else
{
lean_object* v_a_8240_; lean_object* v_a_8241_; lean_object* v___x_8243_; uint8_t v_isShared_8244_; uint8_t v_isSharedCheck_8248_; 
lean_dec_ref(v_linkLibs_8196_);
lean_dec_ref(v_libName_8193_);
v_a_8240_ = lean_ctor_get(v___x_8227_, 0);
v_a_8241_ = lean_ctor_get(v___x_8227_, 1);
v_isSharedCheck_8248_ = !lean_is_exclusive(v___x_8227_);
if (v_isSharedCheck_8248_ == 0)
{
v___x_8243_ = v___x_8227_;
v_isShared_8244_ = v_isSharedCheck_8248_;
goto v_resetjp_8242_;
}
else
{
lean_inc(v_a_8241_);
lean_inc(v_a_8240_);
lean_dec(v___x_8227_);
v___x_8243_ = lean_box(0);
v_isShared_8244_ = v_isSharedCheck_8248_;
goto v_resetjp_8242_;
}
v_resetjp_8242_:
{
lean_object* v___x_8246_; 
if (v_isShared_8244_ == 0)
{
v___x_8246_ = v___x_8243_;
goto v_reusejp_8245_;
}
else
{
lean_object* v_reuseFailAlloc_8247_; 
v_reuseFailAlloc_8247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8247_, 0, v_a_8240_);
lean_ctor_set(v_reuseFailAlloc_8247_, 1, v_a_8241_);
v___x_8246_ = v_reuseFailAlloc_8247_;
goto v_reusejp_8245_;
}
v_reusejp_8245_:
{
return v___x_8246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object* v_libName_8251_, lean_object* v_libFile_8252_, lean_object* v_linkObjs_8253_, lean_object* v_linkLibs_8254_, lean_object* v_args_8255_, lean_object* v_plugin_8256_, lean_object* v_linkDeps_8257_, lean_object* v_a_8258_, lean_object* v_a_8259_, lean_object* v_a_8260_, lean_object* v_a_8261_, lean_object* v_a_8262_, lean_object* v_a_8263_, lean_object* v_a_8264_){
_start:
{
uint8_t v_plugin_boxed_8265_; uint8_t v_linkDeps_boxed_8266_; lean_object* v_res_8267_; 
v_plugin_boxed_8265_ = lean_unbox(v_plugin_8256_);
v_linkDeps_boxed_8266_ = lean_unbox(v_linkDeps_8257_);
v_res_8267_ = l_Lake_buildLeanSharedLibSync(v_libName_8251_, v_libFile_8252_, v_linkObjs_8253_, v_linkLibs_8254_, v_args_8255_, v_plugin_boxed_8265_, v_linkDeps_boxed_8266_, v_a_8258_, v_a_8259_, v_a_8260_, v_a_8261_, v_a_8262_, v_a_8263_);
lean_dec_ref(v_a_8262_);
lean_dec(v_a_8261_);
lean_dec(v_a_8260_);
lean_dec(v_a_8259_);
return v_res_8267_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_traceArgs_8268_, lean_object* v_weakArgs_8269_, lean_object* v_libName_8270_, lean_object* v_libFile_8271_, lean_object* v_objs_8272_, uint8_t v_plugin_8273_, uint8_t v_linkDeps_8274_, lean_object* v_libs_8275_, lean_object* v___y_8276_, lean_object* v___y_8277_, lean_object* v___y_8278_, lean_object* v___y_8279_, lean_object* v___y_8280_, lean_object* v___y_8281_){
_start:
{
uint64_t v___y_8284_; uint64_t v___x_8309_; lean_object* v___x_8310_; lean_object* v___x_8311_; uint8_t v___x_8312_; 
v___x_8309_ = l_Lake_Hash_nil;
v___x_8310_ = lean_unsigned_to_nat(0u);
v___x_8311_ = lean_array_get_size(v_traceArgs_8268_);
v___x_8312_ = lean_nat_dec_lt(v___x_8310_, v___x_8311_);
if (v___x_8312_ == 0)
{
v___y_8284_ = v___x_8309_;
goto v___jp_8283_;
}
else
{
uint8_t v___x_8313_; 
v___x_8313_ = lean_nat_dec_le(v___x_8311_, v___x_8311_);
if (v___x_8313_ == 0)
{
if (v___x_8312_ == 0)
{
v___y_8284_ = v___x_8309_;
goto v___jp_8283_;
}
else
{
size_t v___x_8314_; size_t v___x_8315_; uint64_t v___x_8316_; 
v___x_8314_ = ((size_t)0ULL);
v___x_8315_ = lean_usize_of_nat(v___x_8311_);
v___x_8316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8268_, v___x_8314_, v___x_8315_, v___x_8309_);
v___y_8284_ = v___x_8316_;
goto v___jp_8283_;
}
}
else
{
size_t v___x_8317_; size_t v___x_8318_; uint64_t v___x_8319_; 
v___x_8317_ = ((size_t)0ULL);
v___x_8318_ = lean_usize_of_nat(v___x_8311_);
v___x_8319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8268_, v___x_8317_, v___x_8318_, v___x_8309_);
v___y_8284_ = v___x_8319_;
goto v___jp_8283_;
}
}
v___jp_8283_:
{
lean_object* v_log_8285_; uint8_t v_action_8286_; uint8_t v_wantsRebuild_8287_; lean_object* v_trace_8288_; lean_object* v_buildTime_8289_; lean_object* v___x_8291_; uint8_t v_isShared_8292_; uint8_t v_isSharedCheck_8308_; 
v_log_8285_ = lean_ctor_get(v___y_8281_, 0);
v_action_8286_ = lean_ctor_get_uint8(v___y_8281_, sizeof(void*)*3);
v_wantsRebuild_8287_ = lean_ctor_get_uint8(v___y_8281_, sizeof(void*)*3 + 1);
v_trace_8288_ = lean_ctor_get(v___y_8281_, 1);
v_buildTime_8289_ = lean_ctor_get(v___y_8281_, 2);
v_isSharedCheck_8308_ = !lean_is_exclusive(v___y_8281_);
if (v_isSharedCheck_8308_ == 0)
{
v___x_8291_ = v___y_8281_;
v_isShared_8292_ = v_isSharedCheck_8308_;
goto v_resetjp_8290_;
}
else
{
lean_inc(v_buildTime_8289_);
lean_inc(v_trace_8288_);
lean_inc(v_log_8285_);
lean_dec(v___y_8281_);
v___x_8291_ = lean_box(0);
v_isShared_8292_ = v_isSharedCheck_8308_;
goto v_resetjp_8290_;
}
v_resetjp_8290_:
{
lean_object* v___x_8293_; lean_object* v___x_8294_; lean_object* v___x_8295_; lean_object* v___x_8296_; lean_object* v___x_8297_; lean_object* v___x_8298_; lean_object* v___x_8299_; lean_object* v___x_8300_; lean_object* v___x_8301_; lean_object* v___x_8302_; lean_object* v___x_8304_; 
v___x_8293_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8294_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8295_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8268_);
v___x_8296_ = lean_array_to_list(v_traceArgs_8268_);
v___x_8297_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8296_);
lean_dec(v___x_8296_);
v___x_8298_ = lean_string_append(v___x_8295_, v___x_8297_);
lean_dec_ref(v___x_8297_);
v___x_8299_ = lean_string_append(v___x_8294_, v___x_8298_);
lean_dec_ref(v___x_8298_);
v___x_8300_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8301_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8301_, 0, v___x_8299_);
lean_ctor_set(v___x_8301_, 1, v___x_8293_);
lean_ctor_set(v___x_8301_, 2, v___x_8300_);
lean_ctor_set_uint64(v___x_8301_, sizeof(void*)*3, v___y_8284_);
v___x_8302_ = l_Lake_BuildTrace_mix(v_trace_8288_, v___x_8301_);
if (v_isShared_8292_ == 0)
{
lean_ctor_set(v___x_8291_, 1, v___x_8302_);
v___x_8304_ = v___x_8291_;
goto v_reusejp_8303_;
}
else
{
lean_object* v_reuseFailAlloc_8307_; 
v_reuseFailAlloc_8307_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8307_, 0, v_log_8285_);
lean_ctor_set(v_reuseFailAlloc_8307_, 1, v___x_8302_);
lean_ctor_set(v_reuseFailAlloc_8307_, 2, v_buildTime_8289_);
lean_ctor_set_uint8(v_reuseFailAlloc_8307_, sizeof(void*)*3, v_action_8286_);
lean_ctor_set_uint8(v_reuseFailAlloc_8307_, sizeof(void*)*3 + 1, v_wantsRebuild_8287_);
v___x_8304_ = v_reuseFailAlloc_8307_;
goto v_reusejp_8303_;
}
v_reusejp_8303_:
{
lean_object* v___x_8305_; lean_object* v___x_8306_; 
v___x_8305_ = l_Array_append___redArg(v_weakArgs_8269_, v_traceArgs_8268_);
lean_dec_ref(v_traceArgs_8268_);
v___x_8306_ = l_Lake_buildLeanSharedLibSync(v_libName_8270_, v_libFile_8271_, v_objs_8272_, v_libs_8275_, v___x_8305_, v_plugin_8273_, v_linkDeps_8274_, v___y_8276_, v___y_8277_, v___y_8278_, v___y_8279_, v___y_8280_, v___x_8304_);
return v___x_8306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_traceArgs_8320_, lean_object* v_weakArgs_8321_, lean_object* v_libName_8322_, lean_object* v_libFile_8323_, lean_object* v_objs_8324_, lean_object* v_plugin_8325_, lean_object* v_linkDeps_8326_, lean_object* v_libs_8327_, lean_object* v___y_8328_, lean_object* v___y_8329_, lean_object* v___y_8330_, lean_object* v___y_8331_, lean_object* v___y_8332_, lean_object* v___y_8333_, lean_object* v___y_8334_){
_start:
{
uint8_t v_plugin_boxed_8335_; uint8_t v_linkDeps_boxed_8336_; lean_object* v_res_8337_; 
v_plugin_boxed_8335_ = lean_unbox(v_plugin_8325_);
v_linkDeps_boxed_8336_ = lean_unbox(v_linkDeps_8326_);
v_res_8337_ = l_Lake_buildLeanSharedLib___lam__0(v_traceArgs_8320_, v_weakArgs_8321_, v_libName_8322_, v_libFile_8323_, v_objs_8324_, v_plugin_boxed_8335_, v_linkDeps_boxed_8336_, v_libs_8327_, v___y_8328_, v___y_8329_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_);
lean_dec_ref(v___y_8332_);
lean_dec(v___y_8331_);
lean_dec(v___y_8330_);
lean_dec(v___y_8329_);
return v_res_8337_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_traceArgs_8338_, lean_object* v_weakArgs_8339_, lean_object* v_libName_8340_, lean_object* v_libFile_8341_, uint8_t v_plugin_8342_, uint8_t v_linkDeps_8343_, lean_object* v_linkLibs_8344_, lean_object* v___x_8345_, lean_object* v_objs_8346_, lean_object* v___y_8347_, lean_object* v___y_8348_, lean_object* v___y_8349_, lean_object* v___y_8350_, lean_object* v___y_8351_, lean_object* v___y_8352_){
_start:
{
lean_object* v_trace_8354_; lean_object* v___x_8355_; lean_object* v___x_8356_; lean_object* v___f_8357_; lean_object* v___x_8358_; lean_object* v___x_8359_; lean_object* v___x_8360_; uint8_t v___x_8361_; lean_object* v___x_8362_; lean_object* v___x_8363_; 
v_trace_8354_ = lean_ctor_get(v___y_8352_, 1);
v___x_8355_ = lean_box(v_plugin_8342_);
v___x_8356_ = lean_box(v_linkDeps_8343_);
v___f_8357_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 15, 7);
lean_closure_set(v___f_8357_, 0, v_traceArgs_8338_);
lean_closure_set(v___f_8357_, 1, v_weakArgs_8339_);
lean_closure_set(v___f_8357_, 2, v_libName_8340_);
lean_closure_set(v___f_8357_, 3, v_libFile_8341_);
lean_closure_set(v___f_8357_, 4, v_objs_8346_);
lean_closure_set(v___f_8357_, 5, v___x_8355_);
lean_closure_set(v___f_8357_, 6, v___x_8356_);
v___x_8358_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8359_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8344_, v___x_8358_);
v___x_8360_ = lean_unsigned_to_nat(0u);
v___x_8361_ = 0;
v___x_8362_ = l_Lake_Job_mapM___redArg(v___x_8345_, v___x_8359_, v___f_8357_, v___x_8360_, v___x_8361_, v___y_8347_, v___y_8348_, v___y_8349_, v___y_8350_, v___y_8351_, v_trace_8354_);
v___x_8363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8363_, 0, v___x_8362_);
lean_ctor_set(v___x_8363_, 1, v___y_8352_);
return v___x_8363_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_traceArgs_8364_, lean_object* v_weakArgs_8365_, lean_object* v_libName_8366_, lean_object* v_libFile_8367_, lean_object* v_plugin_8368_, lean_object* v_linkDeps_8369_, lean_object* v_linkLibs_8370_, lean_object* v___x_8371_, lean_object* v_objs_8372_, lean_object* v___y_8373_, lean_object* v___y_8374_, lean_object* v___y_8375_, lean_object* v___y_8376_, lean_object* v___y_8377_, lean_object* v___y_8378_, lean_object* v___y_8379_){
_start:
{
uint8_t v_plugin_boxed_8380_; uint8_t v_linkDeps_boxed_8381_; lean_object* v_res_8382_; 
v_plugin_boxed_8380_ = lean_unbox(v_plugin_8368_);
v_linkDeps_boxed_8381_ = lean_unbox(v_linkDeps_8369_);
v_res_8382_ = l_Lake_buildLeanSharedLib___lam__1(v_traceArgs_8364_, v_weakArgs_8365_, v_libName_8366_, v_libFile_8367_, v_plugin_boxed_8380_, v_linkDeps_boxed_8381_, v_linkLibs_8370_, v___x_8371_, v_objs_8372_, v___y_8373_, v___y_8374_, v___y_8375_, v___y_8376_, v___y_8377_, v___y_8378_);
lean_dec_ref(v___y_8377_);
lean_dec(v___y_8376_);
lean_dec(v___y_8375_);
lean_dec(v___y_8374_);
lean_dec_ref(v_linkLibs_8370_);
return v_res_8382_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8383_, lean_object* v_libFile_8384_, lean_object* v_linkObjs_8385_, lean_object* v_linkLibs_8386_, lean_object* v_weakArgs_8387_, lean_object* v_traceArgs_8388_, uint8_t v_plugin_8389_, uint8_t v_linkDeps_8390_, lean_object* v_a_8391_, lean_object* v_a_8392_, lean_object* v_a_8393_, lean_object* v_a_8394_, lean_object* v_a_8395_, lean_object* v_a_8396_){
_start:
{
lean_object* v___x_8398_; lean_object* v___x_8399_; lean_object* v___x_8400_; lean_object* v___f_8401_; lean_object* v___x_8402_; lean_object* v___x_8403_; lean_object* v___x_8404_; uint8_t v___x_8405_; lean_object* v___x_8406_; 
v___x_8398_ = l_Lake_instDataKindDynlib;
v___x_8399_ = lean_box(v_plugin_8389_);
v___x_8400_ = lean_box(v_linkDeps_8390_);
v___f_8401_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 16, 8);
lean_closure_set(v___f_8401_, 0, v_traceArgs_8388_);
lean_closure_set(v___f_8401_, 1, v_weakArgs_8387_);
lean_closure_set(v___f_8401_, 2, v_libName_8383_);
lean_closure_set(v___f_8401_, 3, v_libFile_8384_);
lean_closure_set(v___f_8401_, 4, v___x_8399_);
lean_closure_set(v___f_8401_, 5, v___x_8400_);
lean_closure_set(v___f_8401_, 6, v_linkLibs_8386_);
lean_closure_set(v___f_8401_, 7, v___x_8398_);
v___x_8402_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8403_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8385_, v___x_8402_);
v___x_8404_ = lean_unsigned_to_nat(0u);
v___x_8405_ = 1;
v___x_8406_ = l_Lake_Job_bindM___redArg(v___x_8398_, v___x_8403_, v___f_8401_, v___x_8404_, v___x_8405_, v_a_8391_, v_a_8392_, v_a_8393_, v_a_8394_, v_a_8395_, v_a_8396_);
return v___x_8406_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8407_, lean_object* v_libFile_8408_, lean_object* v_linkObjs_8409_, lean_object* v_linkLibs_8410_, lean_object* v_weakArgs_8411_, lean_object* v_traceArgs_8412_, lean_object* v_plugin_8413_, lean_object* v_linkDeps_8414_, lean_object* v_a_8415_, lean_object* v_a_8416_, lean_object* v_a_8417_, lean_object* v_a_8418_, lean_object* v_a_8419_, lean_object* v_a_8420_, lean_object* v_a_8421_){
_start:
{
uint8_t v_plugin_boxed_8422_; uint8_t v_linkDeps_boxed_8423_; lean_object* v_res_8424_; 
v_plugin_boxed_8422_ = lean_unbox(v_plugin_8413_);
v_linkDeps_boxed_8423_ = lean_unbox(v_linkDeps_8414_);
v_res_8424_ = l_Lake_buildLeanSharedLib(v_libName_8407_, v_libFile_8408_, v_linkObjs_8409_, v_linkLibs_8410_, v_weakArgs_8411_, v_traceArgs_8412_, v_plugin_boxed_8422_, v_linkDeps_boxed_8423_, v_a_8415_, v_a_8416_, v_a_8417_, v_a_8418_, v_a_8419_, v_a_8420_);
lean_dec_ref(v_a_8420_);
lean_dec_ref(v_a_8419_);
lean_dec(v_a_8418_);
lean_dec(v_a_8417_);
lean_dec(v_a_8416_);
lean_dec_ref(v_linkObjs_8409_);
return v_res_8424_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object* v_linkLibs_8425_, lean_object* v_linkObjs_8426_, lean_object* v_args_8427_, uint8_t v_sharedLean_8428_, lean_object* v_exeFile_8429_, lean_object* v___y_8430_, lean_object* v___y_8431_, lean_object* v___y_8432_, lean_object* v___y_8433_, lean_object* v___y_8434_, lean_object* v___y_8435_){
_start:
{
lean_object* v___x_8437_; 
v___x_8437_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8425_, v___y_8435_);
if (lean_obj_tag(v___x_8437_) == 0)
{
lean_object* v_toContext_8438_; lean_object* v_lakeEnv_8439_; lean_object* v_lean_8440_; lean_object* v_a_8441_; lean_object* v_a_8442_; lean_object* v_leanLibDir_8443_; lean_object* v_cc_8444_; lean_object* v_log_8445_; uint8_t v_action_8446_; uint8_t v_wantsRebuild_8447_; lean_object* v_trace_8448_; lean_object* v_buildTime_8449_; lean_object* v___x_8451_; uint8_t v_isShared_8452_; uint8_t v_isSharedCheck_8487_; 
v_toContext_8438_ = lean_ctor_get(v___y_8434_, 1);
v_lakeEnv_8439_ = lean_ctor_get(v_toContext_8438_, 0);
v_lean_8440_ = lean_ctor_get(v_lakeEnv_8439_, 1);
v_a_8441_ = lean_ctor_get(v___x_8437_, 1);
lean_inc(v_a_8441_);
v_a_8442_ = lean_ctor_get(v___x_8437_, 0);
lean_inc(v_a_8442_);
lean_dec_ref_known(v___x_8437_, 2);
v_leanLibDir_8443_ = lean_ctor_get(v_lean_8440_, 3);
v_cc_8444_ = lean_ctor_get(v_lean_8440_, 14);
v_log_8445_ = lean_ctor_get(v_a_8441_, 0);
v_action_8446_ = lean_ctor_get_uint8(v_a_8441_, sizeof(void*)*3);
v_wantsRebuild_8447_ = lean_ctor_get_uint8(v_a_8441_, sizeof(void*)*3 + 1);
v_trace_8448_ = lean_ctor_get(v_a_8441_, 1);
v_buildTime_8449_ = lean_ctor_get(v_a_8441_, 2);
v_isSharedCheck_8487_ = !lean_is_exclusive(v_a_8441_);
if (v_isSharedCheck_8487_ == 0)
{
v___x_8451_ = v_a_8441_;
v_isShared_8452_ = v_isSharedCheck_8487_;
goto v_resetjp_8450_;
}
else
{
lean_inc(v_buildTime_8449_);
lean_inc(v_trace_8448_);
lean_inc(v_log_8445_);
lean_dec(v_a_8441_);
v___x_8451_ = lean_box(0);
v_isShared_8452_ = v_isSharedCheck_8487_;
goto v_resetjp_8450_;
}
v_resetjp_8450_:
{
lean_object* v___x_8453_; lean_object* v___x_8454_; lean_object* v___x_8455_; lean_object* v___x_8456_; lean_object* v___x_8457_; lean_object* v___x_8458_; lean_object* v___x_8459_; lean_object* v___x_8460_; lean_object* v___x_8461_; lean_object* v___x_8462_; 
v___x_8453_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8426_, v_a_8442_);
lean_dec(v_a_8442_);
v___x_8454_ = l_Array_append___redArg(v___x_8453_, v_args_8427_);
v___x_8455_ = lean_unsigned_to_nat(2u);
v___x_8456_ = lean_mk_empty_array_with_capacity(v___x_8455_);
lean_dec_ref(v___x_8456_);
v___x_8457_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8443_);
v___x_8458_ = lean_array_push(v___x_8457_, v_leanLibDir_8443_);
v___x_8459_ = l_Array_append___redArg(v___x_8454_, v___x_8458_);
lean_dec_ref(v___x_8458_);
v___x_8460_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8428_, v_lean_8440_);
v___x_8461_ = l_Array_append___redArg(v___x_8459_, v___x_8460_);
lean_dec_ref(v___x_8460_);
lean_inc_ref(v_cc_8444_);
v___x_8462_ = l_Lake_compileExe(v_exeFile_8429_, v___x_8461_, v_cc_8444_, v_log_8445_);
lean_dec_ref(v___x_8461_);
if (lean_obj_tag(v___x_8462_) == 0)
{
lean_object* v_a_8463_; lean_object* v_a_8464_; lean_object* v___x_8466_; uint8_t v_isShared_8467_; uint8_t v_isSharedCheck_8474_; 
v_a_8463_ = lean_ctor_get(v___x_8462_, 0);
v_a_8464_ = lean_ctor_get(v___x_8462_, 1);
v_isSharedCheck_8474_ = !lean_is_exclusive(v___x_8462_);
if (v_isSharedCheck_8474_ == 0)
{
v___x_8466_ = v___x_8462_;
v_isShared_8467_ = v_isSharedCheck_8474_;
goto v_resetjp_8465_;
}
else
{
lean_inc(v_a_8464_);
lean_inc(v_a_8463_);
lean_dec(v___x_8462_);
v___x_8466_ = lean_box(0);
v_isShared_8467_ = v_isSharedCheck_8474_;
goto v_resetjp_8465_;
}
v_resetjp_8465_:
{
lean_object* v___x_8469_; 
if (v_isShared_8452_ == 0)
{
lean_ctor_set(v___x_8451_, 0, v_a_8464_);
v___x_8469_ = v___x_8451_;
goto v_reusejp_8468_;
}
else
{
lean_object* v_reuseFailAlloc_8473_; 
v_reuseFailAlloc_8473_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8473_, 0, v_a_8464_);
lean_ctor_set(v_reuseFailAlloc_8473_, 1, v_trace_8448_);
lean_ctor_set(v_reuseFailAlloc_8473_, 2, v_buildTime_8449_);
lean_ctor_set_uint8(v_reuseFailAlloc_8473_, sizeof(void*)*3, v_action_8446_);
lean_ctor_set_uint8(v_reuseFailAlloc_8473_, sizeof(void*)*3 + 1, v_wantsRebuild_8447_);
v___x_8469_ = v_reuseFailAlloc_8473_;
goto v_reusejp_8468_;
}
v_reusejp_8468_:
{
lean_object* v___x_8471_; 
if (v_isShared_8467_ == 0)
{
lean_ctor_set(v___x_8466_, 1, v___x_8469_);
v___x_8471_ = v___x_8466_;
goto v_reusejp_8470_;
}
else
{
lean_object* v_reuseFailAlloc_8472_; 
v_reuseFailAlloc_8472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8472_, 0, v_a_8463_);
lean_ctor_set(v_reuseFailAlloc_8472_, 1, v___x_8469_);
v___x_8471_ = v_reuseFailAlloc_8472_;
goto v_reusejp_8470_;
}
v_reusejp_8470_:
{
return v___x_8471_;
}
}
}
}
else
{
lean_object* v_a_8475_; lean_object* v_a_8476_; lean_object* v___x_8478_; uint8_t v_isShared_8479_; uint8_t v_isSharedCheck_8486_; 
v_a_8475_ = lean_ctor_get(v___x_8462_, 0);
v_a_8476_ = lean_ctor_get(v___x_8462_, 1);
v_isSharedCheck_8486_ = !lean_is_exclusive(v___x_8462_);
if (v_isSharedCheck_8486_ == 0)
{
v___x_8478_ = v___x_8462_;
v_isShared_8479_ = v_isSharedCheck_8486_;
goto v_resetjp_8477_;
}
else
{
lean_inc(v_a_8476_);
lean_inc(v_a_8475_);
lean_dec(v___x_8462_);
v___x_8478_ = lean_box(0);
v_isShared_8479_ = v_isSharedCheck_8486_;
goto v_resetjp_8477_;
}
v_resetjp_8477_:
{
lean_object* v___x_8481_; 
if (v_isShared_8452_ == 0)
{
lean_ctor_set(v___x_8451_, 0, v_a_8476_);
v___x_8481_ = v___x_8451_;
goto v_reusejp_8480_;
}
else
{
lean_object* v_reuseFailAlloc_8485_; 
v_reuseFailAlloc_8485_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8485_, 0, v_a_8476_);
lean_ctor_set(v_reuseFailAlloc_8485_, 1, v_trace_8448_);
lean_ctor_set(v_reuseFailAlloc_8485_, 2, v_buildTime_8449_);
lean_ctor_set_uint8(v_reuseFailAlloc_8485_, sizeof(void*)*3, v_action_8446_);
lean_ctor_set_uint8(v_reuseFailAlloc_8485_, sizeof(void*)*3 + 1, v_wantsRebuild_8447_);
v___x_8481_ = v_reuseFailAlloc_8485_;
goto v_reusejp_8480_;
}
v_reusejp_8480_:
{
lean_object* v___x_8483_; 
if (v_isShared_8479_ == 0)
{
lean_ctor_set(v___x_8478_, 1, v___x_8481_);
v___x_8483_ = v___x_8478_;
goto v_reusejp_8482_;
}
else
{
lean_object* v_reuseFailAlloc_8484_; 
v_reuseFailAlloc_8484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8484_, 0, v_a_8475_);
lean_ctor_set(v_reuseFailAlloc_8484_, 1, v___x_8481_);
v___x_8483_ = v_reuseFailAlloc_8484_;
goto v_reusejp_8482_;
}
v_reusejp_8482_:
{
return v___x_8483_;
}
}
}
}
}
}
else
{
lean_object* v_a_8488_; lean_object* v_a_8489_; lean_object* v___x_8491_; uint8_t v_isShared_8492_; uint8_t v_isSharedCheck_8496_; 
lean_dec_ref(v_exeFile_8429_);
v_a_8488_ = lean_ctor_get(v___x_8437_, 0);
v_a_8489_ = lean_ctor_get(v___x_8437_, 1);
v_isSharedCheck_8496_ = !lean_is_exclusive(v___x_8437_);
if (v_isSharedCheck_8496_ == 0)
{
v___x_8491_ = v___x_8437_;
v_isShared_8492_ = v_isSharedCheck_8496_;
goto v_resetjp_8490_;
}
else
{
lean_inc(v_a_8489_);
lean_inc(v_a_8488_);
lean_dec(v___x_8437_);
v___x_8491_ = lean_box(0);
v_isShared_8492_ = v_isSharedCheck_8496_;
goto v_resetjp_8490_;
}
v_resetjp_8490_:
{
lean_object* v___x_8494_; 
if (v_isShared_8492_ == 0)
{
v___x_8494_ = v___x_8491_;
goto v_reusejp_8493_;
}
else
{
lean_object* v_reuseFailAlloc_8495_; 
v_reuseFailAlloc_8495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8495_, 0, v_a_8488_);
lean_ctor_set(v_reuseFailAlloc_8495_, 1, v_a_8489_);
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
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object* v_linkLibs_8497_, lean_object* v_linkObjs_8498_, lean_object* v_args_8499_, lean_object* v_sharedLean_8500_, lean_object* v_exeFile_8501_, lean_object* v___y_8502_, lean_object* v___y_8503_, lean_object* v___y_8504_, lean_object* v___y_8505_, lean_object* v___y_8506_, lean_object* v___y_8507_, lean_object* v___y_8508_){
_start:
{
uint8_t v_sharedLean_boxed_8509_; lean_object* v_res_8510_; 
v_sharedLean_boxed_8509_ = lean_unbox(v_sharedLean_8500_);
v_res_8510_ = l_Lake_buildLeanExeSync___lam__0(v_linkLibs_8497_, v_linkObjs_8498_, v_args_8499_, v_sharedLean_boxed_8509_, v_exeFile_8501_, v___y_8502_, v___y_8503_, v___y_8504_, v___y_8505_, v___y_8506_, v___y_8507_);
lean_dec_ref(v___y_8506_);
lean_dec(v___y_8505_);
lean_dec(v___y_8504_);
lean_dec(v___y_8503_);
lean_dec_ref(v___y_8502_);
lean_dec_ref(v_args_8499_);
lean_dec_ref(v_linkObjs_8498_);
lean_dec_ref(v_linkLibs_8497_);
return v_res_8510_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object* v_exeFile_8511_, lean_object* v_linkObjs_8512_, lean_object* v_linkLibs_8513_, lean_object* v_args_8514_, uint8_t v_sharedLean_8515_, lean_object* v_a_8516_, lean_object* v_a_8517_, lean_object* v_a_8518_, lean_object* v_a_8519_, lean_object* v_a_8520_, lean_object* v_a_8521_){
_start:
{
lean_object* v_log_8523_; uint8_t v_action_8524_; uint8_t v_wantsRebuild_8525_; lean_object* v_trace_8526_; lean_object* v_buildTime_8527_; lean_object* v___x_8529_; uint8_t v_isShared_8530_; uint8_t v_isSharedCheck_8563_; 
v_log_8523_ = lean_ctor_get(v_a_8521_, 0);
v_action_8524_ = lean_ctor_get_uint8(v_a_8521_, sizeof(void*)*3);
v_wantsRebuild_8525_ = lean_ctor_get_uint8(v_a_8521_, sizeof(void*)*3 + 1);
v_trace_8526_ = lean_ctor_get(v_a_8521_, 1);
v_buildTime_8527_ = lean_ctor_get(v_a_8521_, 2);
v_isSharedCheck_8563_ = !lean_is_exclusive(v_a_8521_);
if (v_isSharedCheck_8563_ == 0)
{
v___x_8529_ = v_a_8521_;
v_isShared_8530_ = v_isSharedCheck_8563_;
goto v_resetjp_8528_;
}
else
{
lean_inc(v_buildTime_8527_);
lean_inc(v_trace_8526_);
lean_inc(v_log_8523_);
lean_dec(v_a_8521_);
v___x_8529_ = lean_box(0);
v_isShared_8530_ = v_isSharedCheck_8563_;
goto v_resetjp_8528_;
}
v_resetjp_8528_:
{
lean_object* v_leanTrace_8531_; lean_object* v___x_8532_; lean_object* v___f_8533_; lean_object* v___x_8534_; lean_object* v___x_8535_; lean_object* v___x_8536_; lean_object* v___x_8538_; 
v_leanTrace_8531_ = lean_ctor_get(v_a_8520_, 2);
v___x_8532_ = lean_box(v_sharedLean_8515_);
lean_inc_ref(v_exeFile_8511_);
v___f_8533_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 12, 5);
lean_closure_set(v___f_8533_, 0, v_linkLibs_8513_);
lean_closure_set(v___f_8533_, 1, v_linkObjs_8512_);
lean_closure_set(v___f_8533_, 2, v_args_8514_);
lean_closure_set(v___f_8533_, 3, v___x_8532_);
lean_closure_set(v___f_8533_, 4, v_exeFile_8511_);
lean_inc_ref(v_leanTrace_8531_);
v___x_8534_ = l_Lake_BuildTrace_mix(v_trace_8526_, v_leanTrace_8531_);
v___x_8535_ = l_Lake_platformTrace;
v___x_8536_ = l_Lake_BuildTrace_mix(v___x_8534_, v___x_8535_);
if (v_isShared_8530_ == 0)
{
lean_ctor_set(v___x_8529_, 1, v___x_8536_);
v___x_8538_ = v___x_8529_;
goto v_reusejp_8537_;
}
else
{
lean_object* v_reuseFailAlloc_8562_; 
v_reuseFailAlloc_8562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8562_, 0, v_log_8523_);
lean_ctor_set(v_reuseFailAlloc_8562_, 1, v___x_8536_);
lean_ctor_set(v_reuseFailAlloc_8562_, 2, v_buildTime_8527_);
lean_ctor_set_uint8(v_reuseFailAlloc_8562_, sizeof(void*)*3, v_action_8524_);
lean_ctor_set_uint8(v_reuseFailAlloc_8562_, sizeof(void*)*3 + 1, v_wantsRebuild_8525_);
v___x_8538_ = v_reuseFailAlloc_8562_;
goto v_reusejp_8537_;
}
v_reusejp_8537_:
{
uint8_t v___x_8539_; uint8_t v___x_8540_; lean_object* v___x_8541_; lean_object* v___x_8542_; 
v___x_8539_ = 1;
v___x_8540_ = 0;
v___x_8541_ = l_System_FilePath_exeExtension;
v___x_8542_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8511_, v___f_8533_, v___x_8540_, v___x_8541_, v___x_8539_, v___x_8539_, v___x_8540_, v_a_8516_, v_a_8517_, v_a_8518_, v_a_8519_, v_a_8520_, v___x_8538_);
if (lean_obj_tag(v___x_8542_) == 0)
{
lean_object* v_a_8543_; lean_object* v_a_8544_; lean_object* v___x_8546_; uint8_t v_isShared_8547_; uint8_t v_isSharedCheck_8552_; 
v_a_8543_ = lean_ctor_get(v___x_8542_, 0);
v_a_8544_ = lean_ctor_get(v___x_8542_, 1);
v_isSharedCheck_8552_ = !lean_is_exclusive(v___x_8542_);
if (v_isSharedCheck_8552_ == 0)
{
v___x_8546_ = v___x_8542_;
v_isShared_8547_ = v_isSharedCheck_8552_;
goto v_resetjp_8545_;
}
else
{
lean_inc(v_a_8544_);
lean_inc(v_a_8543_);
lean_dec(v___x_8542_);
v___x_8546_ = lean_box(0);
v_isShared_8547_ = v_isSharedCheck_8552_;
goto v_resetjp_8545_;
}
v_resetjp_8545_:
{
lean_object* v_path_8548_; lean_object* v___x_8550_; 
v_path_8548_ = lean_ctor_get(v_a_8543_, 1);
lean_inc_ref(v_path_8548_);
lean_dec(v_a_8543_);
if (v_isShared_8547_ == 0)
{
lean_ctor_set(v___x_8546_, 0, v_path_8548_);
v___x_8550_ = v___x_8546_;
goto v_reusejp_8549_;
}
else
{
lean_object* v_reuseFailAlloc_8551_; 
v_reuseFailAlloc_8551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8551_, 0, v_path_8548_);
lean_ctor_set(v_reuseFailAlloc_8551_, 1, v_a_8544_);
v___x_8550_ = v_reuseFailAlloc_8551_;
goto v_reusejp_8549_;
}
v_reusejp_8549_:
{
return v___x_8550_;
}
}
}
else
{
lean_object* v_a_8553_; lean_object* v_a_8554_; lean_object* v___x_8556_; uint8_t v_isShared_8557_; uint8_t v_isSharedCheck_8561_; 
v_a_8553_ = lean_ctor_get(v___x_8542_, 0);
v_a_8554_ = lean_ctor_get(v___x_8542_, 1);
v_isSharedCheck_8561_ = !lean_is_exclusive(v___x_8542_);
if (v_isSharedCheck_8561_ == 0)
{
v___x_8556_ = v___x_8542_;
v_isShared_8557_ = v_isSharedCheck_8561_;
goto v_resetjp_8555_;
}
else
{
lean_inc(v_a_8554_);
lean_inc(v_a_8553_);
lean_dec(v___x_8542_);
v___x_8556_ = lean_box(0);
v_isShared_8557_ = v_isSharedCheck_8561_;
goto v_resetjp_8555_;
}
v_resetjp_8555_:
{
lean_object* v___x_8559_; 
if (v_isShared_8557_ == 0)
{
v___x_8559_ = v___x_8556_;
goto v_reusejp_8558_;
}
else
{
lean_object* v_reuseFailAlloc_8560_; 
v_reuseFailAlloc_8560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8560_, 0, v_a_8553_);
lean_ctor_set(v_reuseFailAlloc_8560_, 1, v_a_8554_);
v___x_8559_ = v_reuseFailAlloc_8560_;
goto v_reusejp_8558_;
}
v_reusejp_8558_:
{
return v___x_8559_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object* v_exeFile_8564_, lean_object* v_linkObjs_8565_, lean_object* v_linkLibs_8566_, lean_object* v_args_8567_, lean_object* v_sharedLean_8568_, lean_object* v_a_8569_, lean_object* v_a_8570_, lean_object* v_a_8571_, lean_object* v_a_8572_, lean_object* v_a_8573_, lean_object* v_a_8574_, lean_object* v_a_8575_){
_start:
{
uint8_t v_sharedLean_boxed_8576_; lean_object* v_res_8577_; 
v_sharedLean_boxed_8576_ = lean_unbox(v_sharedLean_8568_);
v_res_8577_ = l_Lake_buildLeanExeSync(v_exeFile_8564_, v_linkObjs_8565_, v_linkLibs_8566_, v_args_8567_, v_sharedLean_boxed_8576_, v_a_8569_, v_a_8570_, v_a_8571_, v_a_8572_, v_a_8573_, v_a_8574_);
lean_dec_ref(v_a_8573_);
lean_dec(v_a_8572_);
lean_dec(v_a_8571_);
lean_dec(v_a_8570_);
return v_res_8577_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_traceArgs_8578_, lean_object* v_weakArgs_8579_, lean_object* v_exeFile_8580_, lean_object* v_objs_8581_, uint8_t v_sharedLean_8582_, lean_object* v_libs_8583_, lean_object* v___y_8584_, lean_object* v___y_8585_, lean_object* v___y_8586_, lean_object* v___y_8587_, lean_object* v___y_8588_, lean_object* v___y_8589_){
_start:
{
uint64_t v___y_8592_; uint64_t v___x_8617_; lean_object* v___x_8618_; lean_object* v___x_8619_; uint8_t v___x_8620_; 
v___x_8617_ = l_Lake_Hash_nil;
v___x_8618_ = lean_unsigned_to_nat(0u);
v___x_8619_ = lean_array_get_size(v_traceArgs_8578_);
v___x_8620_ = lean_nat_dec_lt(v___x_8618_, v___x_8619_);
if (v___x_8620_ == 0)
{
v___y_8592_ = v___x_8617_;
goto v___jp_8591_;
}
else
{
uint8_t v___x_8621_; 
v___x_8621_ = lean_nat_dec_le(v___x_8619_, v___x_8619_);
if (v___x_8621_ == 0)
{
if (v___x_8620_ == 0)
{
v___y_8592_ = v___x_8617_;
goto v___jp_8591_;
}
else
{
size_t v___x_8622_; size_t v___x_8623_; uint64_t v___x_8624_; 
v___x_8622_ = ((size_t)0ULL);
v___x_8623_ = lean_usize_of_nat(v___x_8619_);
v___x_8624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8578_, v___x_8622_, v___x_8623_, v___x_8617_);
v___y_8592_ = v___x_8624_;
goto v___jp_8591_;
}
}
else
{
size_t v___x_8625_; size_t v___x_8626_; uint64_t v___x_8627_; 
v___x_8625_ = ((size_t)0ULL);
v___x_8626_ = lean_usize_of_nat(v___x_8619_);
v___x_8627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8578_, v___x_8625_, v___x_8626_, v___x_8617_);
v___y_8592_ = v___x_8627_;
goto v___jp_8591_;
}
}
v___jp_8591_:
{
lean_object* v_log_8593_; uint8_t v_action_8594_; uint8_t v_wantsRebuild_8595_; lean_object* v_trace_8596_; lean_object* v_buildTime_8597_; lean_object* v___x_8599_; uint8_t v_isShared_8600_; uint8_t v_isSharedCheck_8616_; 
v_log_8593_ = lean_ctor_get(v___y_8589_, 0);
v_action_8594_ = lean_ctor_get_uint8(v___y_8589_, sizeof(void*)*3);
v_wantsRebuild_8595_ = lean_ctor_get_uint8(v___y_8589_, sizeof(void*)*3 + 1);
v_trace_8596_ = lean_ctor_get(v___y_8589_, 1);
v_buildTime_8597_ = lean_ctor_get(v___y_8589_, 2);
v_isSharedCheck_8616_ = !lean_is_exclusive(v___y_8589_);
if (v_isSharedCheck_8616_ == 0)
{
v___x_8599_ = v___y_8589_;
v_isShared_8600_ = v_isSharedCheck_8616_;
goto v_resetjp_8598_;
}
else
{
lean_inc(v_buildTime_8597_);
lean_inc(v_trace_8596_);
lean_inc(v_log_8593_);
lean_dec(v___y_8589_);
v___x_8599_ = lean_box(0);
v_isShared_8600_ = v_isSharedCheck_8616_;
goto v_resetjp_8598_;
}
v_resetjp_8598_:
{
lean_object* v___x_8601_; lean_object* v___x_8602_; lean_object* v___x_8603_; lean_object* v___x_8604_; lean_object* v___x_8605_; lean_object* v___x_8606_; lean_object* v___x_8607_; lean_object* v___x_8608_; lean_object* v___x_8609_; lean_object* v___x_8610_; lean_object* v___x_8612_; 
v___x_8601_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8602_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8603_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8578_);
v___x_8604_ = lean_array_to_list(v_traceArgs_8578_);
v___x_8605_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8604_);
lean_dec(v___x_8604_);
v___x_8606_ = lean_string_append(v___x_8603_, v___x_8605_);
lean_dec_ref(v___x_8605_);
v___x_8607_ = lean_string_append(v___x_8602_, v___x_8606_);
lean_dec_ref(v___x_8606_);
v___x_8608_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8609_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8609_, 0, v___x_8607_);
lean_ctor_set(v___x_8609_, 1, v___x_8601_);
lean_ctor_set(v___x_8609_, 2, v___x_8608_);
lean_ctor_set_uint64(v___x_8609_, sizeof(void*)*3, v___y_8592_);
v___x_8610_ = l_Lake_BuildTrace_mix(v_trace_8596_, v___x_8609_);
if (v_isShared_8600_ == 0)
{
lean_ctor_set(v___x_8599_, 1, v___x_8610_);
v___x_8612_ = v___x_8599_;
goto v_reusejp_8611_;
}
else
{
lean_object* v_reuseFailAlloc_8615_; 
v_reuseFailAlloc_8615_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8615_, 0, v_log_8593_);
lean_ctor_set(v_reuseFailAlloc_8615_, 1, v___x_8610_);
lean_ctor_set(v_reuseFailAlloc_8615_, 2, v_buildTime_8597_);
lean_ctor_set_uint8(v_reuseFailAlloc_8615_, sizeof(void*)*3, v_action_8594_);
lean_ctor_set_uint8(v_reuseFailAlloc_8615_, sizeof(void*)*3 + 1, v_wantsRebuild_8595_);
v___x_8612_ = v_reuseFailAlloc_8615_;
goto v_reusejp_8611_;
}
v_reusejp_8611_:
{
lean_object* v___x_8613_; lean_object* v___x_8614_; 
v___x_8613_ = l_Array_append___redArg(v_weakArgs_8579_, v_traceArgs_8578_);
lean_dec_ref(v_traceArgs_8578_);
v___x_8614_ = l_Lake_buildLeanExeSync(v_exeFile_8580_, v_objs_8581_, v_libs_8583_, v___x_8613_, v_sharedLean_8582_, v___y_8584_, v___y_8585_, v___y_8586_, v___y_8587_, v___y_8588_, v___x_8612_);
return v___x_8614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_traceArgs_8628_, lean_object* v_weakArgs_8629_, lean_object* v_exeFile_8630_, lean_object* v_objs_8631_, lean_object* v_sharedLean_8632_, lean_object* v_libs_8633_, lean_object* v___y_8634_, lean_object* v___y_8635_, lean_object* v___y_8636_, lean_object* v___y_8637_, lean_object* v___y_8638_, lean_object* v___y_8639_, lean_object* v___y_8640_){
_start:
{
uint8_t v_sharedLean_boxed_8641_; lean_object* v_res_8642_; 
v_sharedLean_boxed_8641_ = lean_unbox(v_sharedLean_8632_);
v_res_8642_ = l_Lake_buildLeanExe___lam__0(v_traceArgs_8628_, v_weakArgs_8629_, v_exeFile_8630_, v_objs_8631_, v_sharedLean_boxed_8641_, v_libs_8633_, v___y_8634_, v___y_8635_, v___y_8636_, v___y_8637_, v___y_8638_, v___y_8639_);
lean_dec_ref(v___y_8638_);
lean_dec(v___y_8637_);
lean_dec(v___y_8636_);
lean_dec(v___y_8635_);
return v_res_8642_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_traceArgs_8643_, lean_object* v_weakArgs_8644_, lean_object* v_exeFile_8645_, uint8_t v_sharedLean_8646_, lean_object* v_linkLibs_8647_, lean_object* v___x_8648_, lean_object* v_objs_8649_, lean_object* v___y_8650_, lean_object* v___y_8651_, lean_object* v___y_8652_, lean_object* v___y_8653_, lean_object* v___y_8654_, lean_object* v___y_8655_){
_start:
{
lean_object* v_trace_8657_; lean_object* v___x_8658_; lean_object* v___f_8659_; lean_object* v___x_8660_; lean_object* v___x_8661_; lean_object* v___x_8662_; uint8_t v___x_8663_; lean_object* v___x_8664_; lean_object* v___x_8665_; 
v_trace_8657_ = lean_ctor_get(v___y_8655_, 1);
v___x_8658_ = lean_box(v_sharedLean_8646_);
v___f_8659_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 5);
lean_closure_set(v___f_8659_, 0, v_traceArgs_8643_);
lean_closure_set(v___f_8659_, 1, v_weakArgs_8644_);
lean_closure_set(v___f_8659_, 2, v_exeFile_8645_);
lean_closure_set(v___f_8659_, 3, v_objs_8649_);
lean_closure_set(v___f_8659_, 4, v___x_8658_);
v___x_8660_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8661_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8647_, v___x_8660_);
v___x_8662_ = lean_unsigned_to_nat(0u);
v___x_8663_ = 0;
v___x_8664_ = l_Lake_Job_mapM___redArg(v___x_8648_, v___x_8661_, v___f_8659_, v___x_8662_, v___x_8663_, v___y_8650_, v___y_8651_, v___y_8652_, v___y_8653_, v___y_8654_, v_trace_8657_);
v___x_8665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8665_, 0, v___x_8664_);
lean_ctor_set(v___x_8665_, 1, v___y_8655_);
return v___x_8665_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_traceArgs_8666_, lean_object* v_weakArgs_8667_, lean_object* v_exeFile_8668_, lean_object* v_sharedLean_8669_, lean_object* v_linkLibs_8670_, lean_object* v___x_8671_, lean_object* v_objs_8672_, lean_object* v___y_8673_, lean_object* v___y_8674_, lean_object* v___y_8675_, lean_object* v___y_8676_, lean_object* v___y_8677_, lean_object* v___y_8678_, lean_object* v___y_8679_){
_start:
{
uint8_t v_sharedLean_boxed_8680_; lean_object* v_res_8681_; 
v_sharedLean_boxed_8680_ = lean_unbox(v_sharedLean_8669_);
v_res_8681_ = l_Lake_buildLeanExe___lam__1(v_traceArgs_8666_, v_weakArgs_8667_, v_exeFile_8668_, v_sharedLean_boxed_8680_, v_linkLibs_8670_, v___x_8671_, v_objs_8672_, v___y_8673_, v___y_8674_, v___y_8675_, v___y_8676_, v___y_8677_, v___y_8678_);
lean_dec_ref(v___y_8677_);
lean_dec(v___y_8676_);
lean_dec(v___y_8675_);
lean_dec(v___y_8674_);
lean_dec_ref(v_linkLibs_8670_);
return v_res_8681_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8682_, lean_object* v_linkObjs_8683_, lean_object* v_linkLibs_8684_, lean_object* v_weakArgs_8685_, lean_object* v_traceArgs_8686_, uint8_t v_sharedLean_8687_, lean_object* v_a_8688_, lean_object* v_a_8689_, lean_object* v_a_8690_, lean_object* v_a_8691_, lean_object* v_a_8692_, lean_object* v_a_8693_){
_start:
{
lean_object* v___x_8695_; lean_object* v___x_8696_; lean_object* v___f_8697_; lean_object* v___x_8698_; lean_object* v___x_8699_; lean_object* v___x_8700_; uint8_t v___x_8701_; lean_object* v___x_8702_; 
v___x_8695_ = l_Lake_instDataKindFilePath;
v___x_8696_ = lean_box(v_sharedLean_8687_);
v___f_8697_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 14, 6);
lean_closure_set(v___f_8697_, 0, v_traceArgs_8686_);
lean_closure_set(v___f_8697_, 1, v_weakArgs_8685_);
lean_closure_set(v___f_8697_, 2, v_exeFile_8682_);
lean_closure_set(v___f_8697_, 3, v___x_8696_);
lean_closure_set(v___f_8697_, 4, v_linkLibs_8684_);
lean_closure_set(v___f_8697_, 5, v___x_8695_);
v___x_8698_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8699_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8683_, v___x_8698_);
v___x_8700_ = lean_unsigned_to_nat(0u);
v___x_8701_ = 1;
v___x_8702_ = l_Lake_Job_bindM___redArg(v___x_8695_, v___x_8699_, v___f_8697_, v___x_8700_, v___x_8701_, v_a_8688_, v_a_8689_, v_a_8690_, v_a_8691_, v_a_8692_, v_a_8693_);
return v___x_8702_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8703_, lean_object* v_linkObjs_8704_, lean_object* v_linkLibs_8705_, lean_object* v_weakArgs_8706_, lean_object* v_traceArgs_8707_, lean_object* v_sharedLean_8708_, lean_object* v_a_8709_, lean_object* v_a_8710_, lean_object* v_a_8711_, lean_object* v_a_8712_, lean_object* v_a_8713_, lean_object* v_a_8714_, lean_object* v_a_8715_){
_start:
{
uint8_t v_sharedLean_boxed_8716_; lean_object* v_res_8717_; 
v_sharedLean_boxed_8716_ = lean_unbox(v_sharedLean_8708_);
v_res_8717_ = l_Lake_buildLeanExe(v_exeFile_8703_, v_linkObjs_8704_, v_linkLibs_8705_, v_weakArgs_8706_, v_traceArgs_8707_, v_sharedLean_boxed_8716_, v_a_8709_, v_a_8710_, v_a_8711_, v_a_8712_, v_a_8713_, v_a_8714_);
lean_dec_ref(v_a_8714_);
lean_dec_ref(v_a_8713_);
lean_dec(v_a_8712_);
lean_dec(v_a_8711_);
lean_dec(v_a_8710_);
lean_dec_ref(v_linkObjs_8704_);
return v_res_8717_;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
