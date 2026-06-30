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
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
extern lean_object* l_System_FilePath_exeExtension;
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
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
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value;
static const lean_array_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSharedLib___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__3___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
static lean_once_cell_t l_Lake_buildLeanSharedLib___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_321_){
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_326_){
_start:
{
lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_fst_327_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v_x_326_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v_fst_327_);
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_array_push(v___x_331_, v___x_329_);
v___x_333_ = lean_array_push(v___x_332_, v_snd_328_);
v___x_334_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_335_, size_t v_i_336_, lean_object* v_bs_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_336_, v_sz_335_);
if (v___x_338_ == 0)
{
return v_bs_337_;
}
else
{
lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_bs_x27_341_; lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_v_339_ = lean_array_uget(v_bs_337_, v_i_336_);
v___x_340_ = lean_unsigned_to_nat(0u);
v_bs_x27_341_ = lean_array_uset(v_bs_337_, v_i_336_, v___x_340_);
v___x_342_ = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_339_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_336_, v___x_343_);
v___x_345_ = lean_array_uset(v_bs_x27_341_, v_i_336_, v___x_342_);
v_i_336_ = v___x_344_;
v_bs_337_ = v___x_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_bs_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_350_, v_i_boxed_351_, v_bs_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_353_){
_start:
{
size_t v_sz_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_sz_354_ = lean_array_size(v_a_353_);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_354_, v___x_355_, v_a_353_);
v___x_357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_){
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
v___x_365_ = l_Lake_instToJsonLogEntry_toJson(v_v_362_);
lean_dec(v_v_362_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_359_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_364_, v_i_359_, v___x_365_);
v_i_359_ = v___x_367_;
v_bs_360_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_376_){
_start:
{
size_t v_sz_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_sz_377_ = lean_array_size(v_a_376_);
v___x_378_ = ((size_t)0ULL);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_377_, v___x_378_, v_a_376_);
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
v___x_405_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_395_);
v___x_406_ = l_Lake_JsonObject_insertJson(v___x_403_, v___x_404_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_408_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_396_);
lean_dec(v_outputs_x3f_396_);
v___x_409_ = l_Lake_JsonObject_insertJson(v___x_406_, v___x_407_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_411_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_397_);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v_x_455_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v___x_463_ = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_461_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_a_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_bs_475_);
return v___x_477_;
}
else
{
lean_object* v_v_478_; lean_object* v___x_479_; 
v_v_478_ = lean_array_uget_borrowed(v_bs_475_, v_i_474_);
lean_inc(v_v_478_);
v___x_479_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_bs_475_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v_bs_x27_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_a_488_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_479_, 1);
v___x_489_ = lean_unsigned_to_nat(0u);
v_bs_x27_490_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_474_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_490_, v_i_474_, v_a_488_);
v_i_474_ = v___x_492_;
v_bs_475_ = v___x_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_bs_497_){
_start:
{
size_t v_sz_boxed_498_; size_t v_i_boxed_499_; lean_object* v_res_500_; 
v_sz_boxed_498_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_498_, v_i_boxed_499_, v_bs_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 4)
{
lean_object* v_elems_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_elems_504_ = lean_ctor_get(v_x_503_, 0);
lean_inc_ref(v_elems_504_);
lean_dec_ref_known(v_x_503_, 1);
v_sz_505_ = lean_array_size(v_elems_504_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_505_, v___x_506_, v_elems_504_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_508_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_509_ = lean_unsigned_to_nat(80u);
v___x_510_ = l_Lean_Json_pretty(v_x_503_, v___x_509_);
v___x_511_ = lean_string_append(v___x_508_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_518_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_519_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_538_){
_start:
{
lean_object* v_j_540_; 
if (lean_obj_tag(v_x_538_) == 4)
{
lean_object* v_elems_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_elems_548_ = lean_ctor_get(v_x_538_, 0);
v___x_549_ = lean_array_get_size(v_elems_548_);
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_nat_dec_eq(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
v_j_540_ = v_x_538_;
goto v___jp_539_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_elems_548_);
lean_dec_ref_known(v_x_538_, 1);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_fget_borrowed(v_elems_548_, v___x_552_);
lean_inc(v___x_553_);
v___x_554_ = l_Lean_Json_getStr_x3f(v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_elems_548_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_a_563_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_573_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_array_fget(v_elems_548_, v___x_567_);
lean_dec_ref(v_elems_548_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_563_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
v_j_540_ = v_x_538_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_541_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_542_ = lean_unsigned_to_nat(80u);
v___x_543_ = l_Lean_Json_pretty(v_j_540_, v___x_542_);
v___x_544_ = lean_string_append(v___x_541_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_bs_576_);
return v___x_578_;
}
else
{
lean_object* v_v_579_; lean_object* v___x_580_; 
v_v_579_ = lean_array_uget_borrowed(v_bs_576_, v_i_575_);
lean_inc(v_v_579_);
v___x_580_ = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_bs_576_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v_bs_x27_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v_a_589_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_580_, 1);
v___x_590_ = lean_unsigned_to_nat(0u);
v_bs_x27_591_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_575_, v___x_592_);
v___x_594_ = lean_array_uset(v_bs_x27_591_, v_i_575_, v_a_589_);
v_i_575_ = v___x_593_;
v_bs_576_ = v___x_594_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_596_, lean_object* v_i_597_, lean_object* v_bs_598_){
_start:
{
size_t v_sz_boxed_599_; size_t v_i_boxed_600_; lean_object* v_res_601_; 
v_sz_boxed_599_ = lean_unbox_usize(v_sz_596_);
lean_dec(v_sz_596_);
v_i_boxed_600_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_599_, v_i_boxed_600_, v_bs_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 4)
{
lean_object* v_elems_603_; size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; 
v_elems_603_ = lean_ctor_get(v_x_602_, 0);
lean_inc_ref(v_elems_603_);
lean_dec_ref_known(v_x_602_, 1);
v_sz_604_ = lean_array_size(v_elems_603_);
v___x_605_ = ((size_t)0ULL);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_604_, v___x_605_, v_elems_603_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_607_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_608_ = lean_unsigned_to_nat(80u);
v___x_609_ = l_Lean_Json_pretty(v_x_602_, v___x_608_);
v___x_610_ = lean_string_append(v___x_607_, v___x_609_);
lean_dec_ref(v___x_609_);
v___x_611_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_616_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
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
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_651_){
_start:
{
lean_object* v___y_653_; uint64_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; uint64_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_667_; uint64_t v___y_668_; lean_object* v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; uint64_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_702_; uint64_t v___y_703_; lean_object* v_a_704_; lean_object* v___y_730_; uint64_t v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
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
lean_ctor_set(v___x_658_, 2, v___y_656_);
lean_ctor_set_uint64(v___x_658_, sizeof(void*)*3, v___y_654_);
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
v___x_674_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_673_);
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
v___y_654_ = v___y_668_;
v___y_655_ = v___y_669_;
v___y_656_ = v_a_670_;
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
v___y_697_ = v___y_702_;
v___y_698_ = v___y_703_;
v___y_699_ = v_a_704_;
goto v___jp_696_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_707_);
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
v___y_698_ = v___y_703_;
v___y_699_ = v_a_704_;
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
v___x_739_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_738_);
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
v___x_768_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_767_);
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
v___x_950_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_949_);
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
uint8_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = 0;
v___x_1265_ = l_Lake_instDecidableEqOutputStatus(v_status_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 1;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1268_){
_start:
{
uint8_t v_status_boxed_1269_; uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_status_boxed_1269_ = lean_unbox(v_status_1268_);
v_res_1270_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1269_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1272_){
_start:
{
uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = 1;
v___x_1274_ = l_Lake_instDecidableEqOutputStatus(v_status_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
uint8_t v___x_1275_; 
v___x_1275_ = 1;
return v___x_1275_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = 0;
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1277_){
_start:
{
uint8_t v_status_boxed_1278_; uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_status_boxed_1278_ = lean_unbox(v_status_1277_);
v_res_1279_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___f_1282_; 
v___x_1281_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1282_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1282_, 0, v___x_1281_);
return v___f_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_info_1285_, lean_object* v_depTrace_1286_, lean_object* v_depHash_1287_, lean_object* v_oldTrace_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint64_t v_hash_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_hash_1292_ = lean_ctor_get_uint64(v_depTrace_1286_, sizeof(void*)*3);
v___f_1293_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1294_ = lean_box_uint64(v_hash_1292_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
v___x_1296_ = l_Option_instBEq_beq___redArg(v___f_1293_, v___x_1295_, v_depHash_1287_);
if (v___x_1296_ == 0)
{
lean_object* v_toBuildConfig_1297_; uint8_t v_oldMode_1298_; 
lean_dec_ref(v_inst_1283_);
v_toBuildConfig_1297_ = lean_ctor_get(v_a_1289_, 0);
v_oldMode_1298_ = lean_ctor_get_uint8(v_toBuildConfig_1297_, sizeof(void*)*3);
if (v_oldMode_1298_ == 0)
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_info_1285_);
lean_dec_ref(v_inst_1284_);
v___x_1299_ = 0;
v___x_1300_ = lean_box(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1290_);
return v___x_1301_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1284_, v_info_1285_, v_oldTrace_1288_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = 0;
v___x_1304_ = lean_box(v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_a_1290_);
return v___x_1305_;
}
else
{
uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = 1;
v___x_1307_ = lean_box(v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_a_1290_);
return v___x_1308_;
}
}
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_dec_ref(v_inst_1284_);
v___x_1309_ = lean_apply_2(v_inst_1283_, v_info_1285_, lean_box(0));
v___x_1310_ = lean_unbox(v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = 0;
v___x_1312_ = lean_box(v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_a_1290_);
return v___x_1313_;
}
else
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = 2;
v___x_1315_ = lean_box(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_a_1290_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_info_1319_, lean_object* v_depTrace_1320_, lean_object* v_depHash_1321_, lean_object* v_oldTrace_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1317_, v_inst_1318_, v_info_1319_, v_depTrace_1320_, v_depHash_1321_, v_oldTrace_1322_, v_a_1323_, v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec_ref(v_oldTrace_1322_);
lean_dec_ref(v_depTrace_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_info_1330_, lean_object* v_depTrace_1331_, lean_object* v_depHash_1332_, lean_object* v_oldTrace_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1328_, v_inst_1329_, v_info_1330_, v_depTrace_1331_, v_depHash_1332_, v_oldTrace_1333_, v_a_1338_, v_a_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_info_1345_, lean_object* v_depTrace_1346_, lean_object* v_depHash_1347_, lean_object* v_oldTrace_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1342_, v_inst_1343_, v_inst_1344_, v_info_1345_, v_depTrace_1346_, v_depHash_1347_, v_oldTrace_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_oldTrace_1348_);
lean_dec_ref(v_depTrace_1346_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_info_1359_, lean_object* v_depTrace_1360_, lean_object* v_depHash_1361_, lean_object* v_oldTrace_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1385_; 
v___x_1366_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1357_, v_inst_1358_, v_info_1359_, v_depTrace_1360_, v_depHash_1361_, v_oldTrace_1362_, v_a_1363_, v_a_1364_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_a_1368_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint8_t v___x_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = 0;
v___x_1373_ = lean_unbox(v_a_1367_);
lean_dec(v_a_1367_);
v___x_1374_ = l_Lake_instDecidableEqOutputStatus(v___x_1373_, v___x_1372_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = 1;
v___x_1376_ = lean_box(v___x_1375_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1376_);
v___x_1378_ = v___x_1370_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1368_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
else
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1381_);
v___x_1383_ = v___x_1370_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_a_1368_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_info_1388_, lean_object* v_depTrace_1389_, lean_object* v_depHash_1390_, lean_object* v_oldTrace_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lake_checkHashUpToDate___redArg(v_inst_1386_, v_inst_1387_, v_info_1388_, v_depTrace_1389_, v_depHash_1390_, v_oldTrace_1391_, v_a_1392_, v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec_ref(v_oldTrace_1391_);
lean_dec_ref(v_depTrace_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_info_1399_, lean_object* v_depTrace_1400_, lean_object* v_depHash_1401_, lean_object* v_oldTrace_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_a_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1429_; 
v___x_1410_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1397_, v_inst_1398_, v_info_1399_, v_depTrace_1400_, v_depHash_1401_, v_oldTrace_1402_, v_a_1407_, v_a_1408_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_a_1412_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1414_ = v___x_1410_;
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
uint8_t v___x_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = 0;
v___x_1417_ = lean_unbox(v_a_1411_);
lean_dec(v_a_1411_);
v___x_1418_ = l_Lake_instDecidableEqOutputStatus(v___x_1417_, v___x_1416_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = 1;
v___x_1420_ = lean_box(v___x_1419_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1420_);
v___x_1422_ = v___x_1414_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1412_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1425_);
v___x_1427_ = v___x_1414_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_a_1412_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_info_1433_, lean_object* v_depTrace_1434_, lean_object* v_depHash_1435_, lean_object* v_oldTrace_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lake_checkHashUpToDate(v_00_u03b9_1430_, v_inst_1431_, v_inst_1432_, v_info_1433_, v_depTrace_1434_, v_depHash_1435_, v_oldTrace_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_oldTrace_1436_);
lean_dec_ref(v_depTrace_1434_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1451_ == 0)
{
lean_object* v_log_1452_; uint8_t v_action_1453_; uint8_t v_wantsRebuild_1454_; lean_object* v_trace_1455_; lean_object* v_buildTime_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1469_; 
v_log_1452_ = lean_ctor_get(v___y_1449_, 0);
v_action_1453_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*3);
v_wantsRebuild_1454_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*3 + 1);
v_trace_1455_ = lean_ctor_get(v___y_1449_, 1);
v_buildTime_1456_ = lean_ctor_get(v___y_1449_, 2);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___y_1449_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1458_ = v___y_1449_;
v_isShared_1459_ = v_isSharedCheck_1469_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_buildTime_1456_);
lean_inc(v_trace_1455_);
lean_inc(v_log_1452_);
lean_dec(v___y_1449_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1469_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1460_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
v___x_1461_ = lean_box(0);
lean_inc(v___x_1460_);
v___x_1462_ = lean_array_push(v_log_1452_, v___x_1460_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1462_);
v___x_1464_ = v___x_1458_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_trace_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_buildTime_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3, v_action_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3 + 1, v_wantsRebuild_1454_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1446_, v___x_1465_);
v_i_1446_ = v___x_1466_;
v_b_1448_ = v___x_1461_;
v___y_1449_ = v___x_1464_;
goto _start;
}
}
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1448_);
lean_ctor_set(v___x_1470_, 1, v___y_1449_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
size_t v_i_boxed_1477_; size_t v_stop_boxed_1478_; lean_object* v_res_1479_; 
v_i_boxed_1477_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1478_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1471_, v_i_boxed_1477_, v_stop_boxed_1478_, v_b_1474_, v___y_1475_);
lean_dec_ref(v_as_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v_log_1480_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v_a_1486_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_le(v___x_1489_, v___x_1489_);
if (v___x_1493_ == 0)
{
if (v___x_1491_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v_a_1486_);
return v___x_1494_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_of_nat(v___x_1489_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1480_, v___x_1495_, v___x_1496_, v___x_1490_, v_a_1486_);
return v___x_1497_;
}
}
else
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = lean_usize_of_nat(v___x_1489_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1480_, v___x_1498_, v___x_1499_, v___x_1490_, v_a_1486_);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec_ref(v_log_1501_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1510_, size_t v_i_1511_, size_t v_stop_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1510_, v_i_1511_, v_stop_1512_, v_b_1513_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1522_, lean_object* v_i_1523_, lean_object* v_stop_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_i_boxed_1533_; size_t v_stop_boxed_1534_; lean_object* v_res_1535_; 
v_i_boxed_1533_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_stop_boxed_1534_ = lean_unbox_usize(v_stop_1524_);
lean_dec(v_stop_1524_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1522_, v_i_boxed_1533_, v_stop_boxed_1534_, v_b_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_as_1522_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_info_1538_, lean_object* v_depTrace_1539_, lean_object* v_savedTrace_1540_, lean_object* v_oldTrace_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
if (lean_obj_tag(v_savedTrace_1540_) == 2)
{
lean_object* v_data_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1599_; 
v_data_1549_ = lean_ctor_get(v_savedTrace_1540_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_savedTrace_1540_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1551_ = v_savedTrace_1540_;
v_isShared_1552_ = v_isSharedCheck_1599_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_data_1549_);
lean_dec(v_savedTrace_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1599_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint64_t v_depHash_1553_; lean_object* v_log_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_depHash_1553_ = lean_ctor_get_uint64(v_data_1549_, sizeof(void*)*3);
v_log_1554_ = lean_ctor_get(v_data_1549_, 2);
lean_inc_ref(v_log_1554_);
lean_dec_ref(v_data_1549_);
v___x_1555_ = lean_box_uint64(v_depHash_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1597_; 
v___x_1558_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1536_, v_inst_1537_, v_info_1538_, v_depTrace_1539_, v___x_1557_, v_oldTrace_1541_, v_a_1546_, v_a_1547_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_a_1560_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___y_1565_; uint8_t v___x_1569_; uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = 0;
v___x_1570_ = lean_unbox(v_a_1559_);
v___x_1571_ = l_Lake_instDecidableEqOutputStatus(v___x_1570_, v___x_1569_);
if (v___x_1571_ == 0)
{
lean_object* v_log_1572_; uint8_t v_action_1573_; uint8_t v_wantsRebuild_1574_; lean_object* v_trace_1575_; lean_object* v_buildTime_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1596_; 
v_log_1572_ = lean_ctor_get(v_a_1560_, 0);
v_action_1573_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*3);
v_wantsRebuild_1574_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*3 + 1);
v_trace_1575_ = lean_ctor_get(v_a_1560_, 1);
v_buildTime_1576_ = lean_ctor_get(v_a_1560_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1578_ = v_a_1560_;
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_buildTime_1576_);
lean_inc(v_trace_1575_);
lean_inc(v_log_1572_);
lean_dec(v_a_1560_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
uint8_t v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = 2;
v___x_1581_ = l_Lake_JobAction_merge(v_action_1573_, v___x_1580_);
if (v_isShared_1579_ == 0)
{
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_log_1572_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_trace_1575_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_buildTime_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1595_, sizeof(void*)*3 + 1, v_wantsRebuild_1574_);
v___x_1583_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*3, v___x_1581_);
v___x_1584_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1554_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v___x_1583_);
lean_dec_ref(v_log_1554_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 2);
v___y_1565_ = v_a_1585_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_del_object(v___x_1562_);
lean_dec(v_a_1559_);
v_a_1586_ = lean_ctor_get(v___x_1584_, 0);
v_a_1587_ = lean_ctor_get(v___x_1584_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1584_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1584_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1554_);
v___y_1565_ = v_a_1560_;
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___y_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___y_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1600_; uint8_t v_oldMode_1601_; 
lean_dec(v_savedTrace_1540_);
lean_dec_ref(v_inst_1536_);
v_toBuildConfig_1600_ = lean_ctor_get(v_a_1546_, 0);
v_oldMode_1601_ = lean_ctor_get_uint8(v_toBuildConfig_1600_, sizeof(void*)*3);
if (v_oldMode_1601_ == 0)
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_info_1538_);
lean_dec_ref(v_inst_1537_);
v___x_1602_ = 0;
v___x_1603_ = lean_box(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1547_);
return v___x_1604_;
}
else
{
uint8_t v___x_1605_; 
v___x_1605_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1537_, v_info_1538_, v_oldTrace_1541_);
if (v___x_1605_ == 0)
{
uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = 0;
v___x_1607_ = lean_box(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_a_1547_);
return v___x_1608_;
}
else
{
uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = 1;
v___x_1610_ = lean_box(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1547_);
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_info_1614_, lean_object* v_depTrace_1615_, lean_object* v_savedTrace_1616_, lean_object* v_oldTrace_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1612_, v_inst_1613_, v_info_1614_, v_depTrace_1615_, v_savedTrace_1616_, v_oldTrace_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_oldTrace_1617_);
lean_dec_ref(v_depTrace_1615_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_info_1629_, lean_object* v_depTrace_1630_, lean_object* v_savedTrace_1631_, lean_object* v_oldTrace_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1627_, v_inst_1628_, v_info_1629_, v_depTrace_1630_, v_savedTrace_1631_, v_oldTrace_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_info_1644_, lean_object* v_depTrace_1645_, lean_object* v_savedTrace_1646_, lean_object* v_oldTrace_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1641_, v_inst_1642_, v_inst_1643_, v_info_1644_, v_depTrace_1645_, v_savedTrace_1646_, v_oldTrace_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec_ref(v_oldTrace_1647_);
lean_dec_ref(v_depTrace_1645_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_info_1658_, lean_object* v_depTrace_1659_, lean_object* v_savedTrace_1660_, lean_object* v_oldTrace_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1656_, v_inst_1657_, v_info_1658_, v_depTrace_1659_, v_savedTrace_1660_, v_oldTrace_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1688_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_a_1671_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1673_ = v___x_1669_;
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; uint8_t v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = 0;
v___x_1676_ = lean_unbox(v_a_1670_);
lean_dec(v_a_1670_);
v___x_1677_ = l_Lake_instDecidableEqOutputStatus(v___x_1676_, v___x_1675_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = 1;
v___x_1679_ = lean_box(v___x_1678_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1679_);
v___x_1681_ = v___x_1673_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1671_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = 0;
v___x_1684_ = lean_box(v___x_1683_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1684_);
v___x_1686_ = v___x_1673_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1671_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1689_ = lean_ctor_get(v___x_1669_, 0);
v_a_1690_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1669_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_inc(v_a_1689_);
lean_dec(v___x_1669_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_info_1700_, lean_object* v_depTrace_1701_, lean_object* v_savedTrace_1702_, lean_object* v_oldTrace_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1698_, v_inst_1699_, v_info_1700_, v_depTrace_1701_, v_savedTrace_1702_, v_oldTrace_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec_ref(v_oldTrace_1703_);
lean_dec_ref(v_depTrace_1701_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_info_1715_, lean_object* v_depTrace_1716_, lean_object* v_savedTrace_1717_, lean_object* v_oldTrace_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1713_, v_inst_1714_, v_info_1715_, v_depTrace_1716_, v_savedTrace_1717_, v_oldTrace_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1745_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_a_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = 0;
v___x_1733_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
v___x_1734_ = l_Lake_instDecidableEqOutputStatus(v___x_1733_, v___x_1732_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = 1;
v___x_1736_ = lean_box(v___x_1735_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1736_);
v___x_1738_ = v___x_1730_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1728_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1740_ = 0;
v___x_1741_ = lean_box(v___x_1740_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1741_);
v___x_1743_ = v___x_1730_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1728_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1746_ = lean_ctor_get(v___x_1726_, 0);
v_a_1747_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1726_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_inc(v_a_1746_);
lean_dec(v___x_1726_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1746_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_info_1758_, lean_object* v_depTrace_1759_, lean_object* v_savedTrace_1760_, lean_object* v_oldTrace_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1755_, v_inst_1756_, v_inst_1757_, v_info_1758_, v_depTrace_1759_, v_savedTrace_1760_, v_oldTrace_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec_ref(v_oldTrace_1761_);
lean_dec_ref(v_depTrace_1759_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t v_inputHash_1770_, lean_object* v_self_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___y_1775_; 
if (lean_obj_tag(v_self_1771_) == 2)
{
lean_object* v_data_1793_; uint64_t v_depHash_1794_; lean_object* v_log_1795_; uint8_t v_synthetic_1796_; uint8_t v___x_1797_; lean_object* v___y_1799_; lean_object* v___y_1803_; 
v_data_1793_ = lean_ctor_get(v_self_1771_, 0);
v_depHash_1794_ = lean_ctor_get_uint64(v_data_1793_, sizeof(void*)*3);
v_log_1795_ = lean_ctor_get(v_data_1793_, 2);
v_synthetic_1796_ = lean_ctor_get_uint8(v_data_1793_, sizeof(void*)*3 + 8);
v___x_1797_ = lean_uint64_dec_eq(v_depHash_1794_, v_inputHash_1770_);
if (v___x_1797_ == 0)
{
v___y_1775_ = v_a_1772_;
goto v___jp_1774_;
}
else
{
if (v_synthetic_1796_ == 0)
{
goto v___jp_1814_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_array_get_size(v_log_1795_);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_nat_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
goto v___jp_1814_;
}
else
{
lean_object* v_log_1843_; uint8_t v_action_1844_; uint8_t v_wantsRebuild_1845_; lean_object* v_trace_1846_; lean_object* v_buildTime_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_log_1843_ = lean_ctor_get(v_a_1772_, 0);
v_action_1844_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3);
v_wantsRebuild_1845_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3 + 1);
v_trace_1846_ = lean_ctor_get(v_a_1772_, 1);
v_buildTime_1847_ = lean_ctor_get(v_a_1772_, 2);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v_a_1772_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_buildTime_1847_);
lean_inc(v_trace_1846_);
lean_inc(v_log_1843_);
lean_dec(v_a_1772_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = 1;
v___x_1852_ = l_Lake_JobAction_merge(v_action_1844_, v___x_1851_);
if (v_isShared_1850_ == 0)
{
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_log_1843_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_trace_1846_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_buildTime_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*3 + 1, v_wantsRebuild_1845_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*3, v___x_1852_);
v___y_1799_ = v___x_1854_;
goto v___jp_1798_;
}
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_box(v___x_1797_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1799_);
return v___x_1801_;
}
v___jp_1802_:
{
if (lean_obj_tag(v___y_1803_) == 0)
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___y_1803_, 1);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___y_1803_, 2);
v___y_1799_ = v_a_1804_;
goto v___jp_1798_;
}
else
{
lean_object* v_a_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1805_ = lean_ctor_get(v___y_1803_, 0);
v_a_1806_ = lean_ctor_get(v___y_1803_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___y_1803_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___y_1803_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_inc(v_a_1805_);
lean_dec(v___y_1803_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1805_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
v___jp_1814_:
{
lean_object* v_log_1815_; uint8_t v_action_1816_; uint8_t v_wantsRebuild_1817_; lean_object* v_trace_1818_; lean_object* v_buildTime_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1839_; 
v_log_1815_ = lean_ctor_get(v_a_1772_, 0);
v_action_1816_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3);
v_wantsRebuild_1817_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3 + 1);
v_trace_1818_ = lean_ctor_get(v_a_1772_, 1);
v_buildTime_1819_ = lean_ctor_get(v_a_1772_, 2);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1821_ = v_a_1772_;
v_isShared_1822_ = v_isSharedCheck_1839_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_buildTime_1819_);
lean_inc(v_trace_1818_);
lean_inc(v_log_1815_);
lean_dec(v_a_1772_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1839_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint8_t v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = 2;
v___x_1824_ = l_Lake_JobAction_merge(v_action_1816_, v___x_1823_);
if (v_isShared_1822_ == 0)
{
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_log_1815_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_trace_1818_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_buildTime_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, sizeof(void*)*3 + 1, v_wantsRebuild_1817_);
v___x_1826_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*3, v___x_1824_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = lean_array_get_size(v_log_1795_);
v___x_1829_ = lean_nat_dec_lt(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
v___y_1799_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_nat_dec_le(v___x_1828_, v___x_1828_);
if (v___x_1831_ == 0)
{
if (v___x_1829_ == 0)
{
v___y_1799_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = lean_usize_of_nat(v___x_1828_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1795_, v___x_1832_, v___x_1833_, v___x_1830_, v___x_1826_);
v___y_1803_ = v___x_1834_;
goto v___jp_1802_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1828_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1795_, v___x_1835_, v___x_1836_, v___x_1830_, v___x_1826_);
v___y_1803_ = v___x_1837_;
goto v___jp_1802_;
}
}
}
}
}
}
else
{
v___y_1775_ = v_a_1772_;
goto v___jp_1774_;
}
v___jp_1774_:
{
lean_object* v_log_1776_; uint8_t v_action_1777_; uint8_t v_wantsRebuild_1778_; lean_object* v_trace_1779_; lean_object* v_buildTime_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1792_; 
v_log_1776_ = lean_ctor_get(v___y_1775_, 0);
v_action_1777_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1778_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1779_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1780_ = lean_ctor_get(v___y_1775_, 2);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1782_ = v___y_1775_;
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_buildTime_1780_);
lean_inc(v_trace_1779_);
lean_inc(v_log_1776_);
lean_dec(v___y_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
uint8_t v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = 1;
v___x_1785_ = l_Lake_JobAction_merge(v_action_1777_, v___x_1784_);
if (v_isShared_1783_ == 0)
{
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_log_1776_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_trace_1779_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_buildTime_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*3 + 1, v_wantsRebuild_1778_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3, v___x_1785_);
v___x_1788_ = 0;
v___x_1789_ = lean_box(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1787_);
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object* v_inputHash_1857_, lean_object* v_self_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint64_t v_inputHash_boxed_1861_; lean_object* v_res_1862_; 
v_inputHash_boxed_1861_ = lean_unbox_uint64(v_inputHash_1857_);
lean_dec_ref(v_inputHash_1857_);
v_res_1862_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_boxed_1861_, v_self_1858_, v_a_1859_);
lean_dec(v_self_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t v_inputHash_1863_, lean_object* v_self_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1863_, v_self_1864_, v_a_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object* v_inputHash_1873_, lean_object* v_self_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint64_t v_inputHash_boxed_1882_; lean_object* v_res_1883_; 
v_inputHash_boxed_1882_ = lean_unbox_uint64(v_inputHash_1873_);
lean_dec_ref(v_inputHash_1873_);
v_res_1883_ = l_Lake_SavedTrace_replayCachedIfUpToDate(v_inputHash_boxed_1882_, v_self_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_self_1874_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1884_, lean_object* v_self_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1884_, v_self_1885_, v_a_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1889_, lean_object* v_self_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint64_t v_inputHash_boxed_1893_; lean_object* v_res_1894_; 
v_inputHash_boxed_1893_ = lean_unbox_uint64(v_inputHash_1889_);
lean_dec_ref(v_inputHash_1889_);
v_res_1894_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1893_, v_self_1890_, v_a_1891_);
lean_dec(v_self_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1895_, lean_object* v_self_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1895_, v_self_1896_, v_a_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1905_, lean_object* v_self_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
uint64_t v_inputHash_boxed_1914_; lean_object* v_res_1915_; 
v_inputHash_boxed_1914_ = lean_unbox_uint64(v_inputHash_1905_);
lean_dec_ref(v_inputHash_1905_);
v_res_1915_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1914_, v_self_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_self_1906_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1921_){
_start:
{
lean_object* v_descr_1922_; uint64_t v_hash_1923_; lean_object* v_ext_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_descr_1922_ = lean_ctor_get(v_x_1921_, 0);
v_hash_1923_ = lean_ctor_get_uint64(v_descr_1922_, sizeof(void*)*1);
v_ext_1924_ = lean_ctor_get(v_descr_1922_, 0);
v___x_1925_ = lean_string_utf8_byte_size(v_ext_1924_);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_nat_dec_eq(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1928_ = l_Lake_lowerHexUInt64(v_hash_1923_);
v___x_1929_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_string_append(v___x_1930_, v_ext_1924_);
v___x_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = l_Lake_lowerHexUInt64(v_hash_1923_);
v___x_1934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1935_);
lean_dec_ref(v_x_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1939_, lean_object* v_a_x3f_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_log_1944_; uint8_t v_action_1945_; uint8_t v_wantsRebuild_1946_; lean_object* v_trace_1947_; lean_object* v_buildTime_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1959_; 
v___x_1943_ = lean_io_mono_ms_now();
v_log_1944_ = lean_ctor_get(v___y_1941_, 0);
v_action_1945_ = lean_ctor_get_uint8(v___y_1941_, sizeof(void*)*3);
v_wantsRebuild_1946_ = lean_ctor_get_uint8(v___y_1941_, sizeof(void*)*3 + 1);
v_trace_1947_ = lean_ctor_get(v___y_1941_, 1);
v_buildTime_1948_ = lean_ctor_get(v___y_1941_, 2);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1941_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1950_ = v___y_1941_;
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_buildTime_1948_);
lean_inc(v_trace_1947_);
lean_inc(v_log_1944_);
lean_dec(v___y_1941_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1952_ = lean_nat_sub(v___x_1943_, v_val_1939_);
lean_dec(v___x_1943_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_nat_add(v_buildTime_1948_, v___x_1952_);
lean_dec(v___x_1952_);
lean_dec(v_buildTime_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 2, v___x_1954_);
v___x_1956_ = v___x_1950_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_log_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_trace_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___x_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*3, v_action_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*3 + 1, v_wantsRebuild_1946_);
v___x_1956_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1960_, lean_object* v_a_x3f_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lake_buildAction___redArg___lam__0(v_val_1960_, v_a_x3f_1961_, v___y_1962_);
lean_dec(v_a_x3f_1961_);
lean_dec(v_val_1960_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1970_, lean_object* v_depTrace_1971_, lean_object* v_traceFile_1972_, lean_object* v_build_1973_, uint8_t v_action_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_a_1983_; lean_object* v_a_1984_; lean_object* v_log_1987_; uint8_t v_action_1988_; uint8_t v_wantsRebuild_1989_; lean_object* v_trace_1990_; lean_object* v_buildTime_1991_; lean_object* v_toBuildConfig_1997_; lean_object* v_log_1998_; uint8_t v_action_1999_; uint8_t v_wantsRebuild_2000_; lean_object* v_trace_2001_; lean_object* v_buildTime_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2108_; 
v_toBuildConfig_1997_ = lean_ctor_get(v_a_1979_, 0);
v_log_1998_ = lean_ctor_get(v_a_1980_, 0);
v_action_1999_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*3);
v_wantsRebuild_2000_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*3 + 1);
v_trace_2001_ = lean_ctor_get(v_a_1980_, 1);
v_buildTime_2002_ = lean_ctor_get(v_a_1980_, 2);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2004_ = v_a_1980_;
v_isShared_2005_ = v_isSharedCheck_2108_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_buildTime_2002_);
lean_inc(v_trace_2001_);
lean_inc(v_log_1998_);
lean_dec(v_a_1980_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2108_;
goto v_resetjp_2003_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_a_1983_);
lean_ctor_set(v___x_1985_, 1, v_a_1984_);
return v___x_1985_;
}
v___jp_1986_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1993_ = lean_array_get_size(v_log_1987_);
v___x_1994_ = lean_array_push(v_log_1987_, v___x_1992_);
v___x_1995_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_trace_1990_);
lean_ctor_set(v___x_1995_, 2, v_buildTime_1991_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3, v_action_1988_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3 + 1, v_wantsRebuild_1989_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
return v___x_1996_;
}
v_resetjp_2003_:
{
uint8_t v_noBuild_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_noBuild_2006_ = lean_ctor_get_uint8(v_toBuildConfig_1997_, sizeof(void*)*3 + 2);
v___x_2007_ = l_Lake_JobAction_merge(v_action_1999_, v_action_1974_);
v___x_2008_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1972_);
v___x_2009_ = l_System_FilePath_addExtension(v_traceFile_1972_, v___x_2008_);
if (v_noBuild_2006_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1998_);
if (v_isShared_2005_ == 0)
{
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_log_1998_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_trace_2001_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_buildTime_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2092_, sizeof(void*)*3 + 1, v_wantsRebuild_2000_);
v___x_2012_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v_a_2015_; lean_object* v_a_2016_; 
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*3, v___x_2007_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc(v_a_1977_);
lean_inc(v_a_1976_);
v___x_2013_ = lean_apply_7(v_build_1973_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v___x_2012_, lean_box(0));
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2020_; lean_object* v_a_2021_; lean_object* v_log_2022_; uint8_t v_action_2023_; uint8_t v_wantsRebuild_2024_; lean_object* v_trace_2025_; lean_object* v_buildTime_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_a_2020_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2020_);
v_a_2021_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_n(v_a_2021_, 2);
lean_dec_ref_known(v___x_2013_, 2);
v_log_2022_ = lean_ctor_get(v_a_2020_, 0);
v_action_2023_ = lean_ctor_get_uint8(v_a_2020_, sizeof(void*)*3);
v_wantsRebuild_2024_ = lean_ctor_get_uint8(v_a_2020_, sizeof(void*)*3 + 1);
v_trace_2025_ = lean_ctor_get(v_a_2020_, 1);
v_buildTime_2026_ = lean_ctor_get(v_a_2020_, 2);
v___x_2027_ = lean_array_get_size(v_log_1998_);
lean_dec_ref(v_log_1998_);
v___x_2028_ = lean_array_get_size(v_log_2022_);
v___x_2029_ = l_Array_extract___redArg(v_log_2022_, v___x_2027_, v___x_2028_);
v___x_2030_ = lean_apply_1(v_inst_1970_, v_a_2021_);
v___x_2031_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1971_, v___x_2030_, v___x_2029_);
v___x_2032_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1972_, v___x_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2073_; 
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2074_);
v___x_2034_ = v___x_2032_;
v_isShared_2035_ = v_isSharedCheck_2073_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_2032_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2073_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lake_removeFileIfExists(v___x_2009_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2057_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
lean_inc(v_a_2021_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_a_2021_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2021_);
v___x_2041_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2041_);
v___x_2043_ = v___x_2034_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v___x_2044_ = l_Lake_buildAction___redArg___lam__0(v___x_2010_, v___x_2043_, v_a_2020_);
lean_dec_ref(v___x_2043_);
lean_dec(v___x_2010_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2053_);
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v_a_2021_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2021_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
else
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
lean_inc(v_buildTime_2026_);
lean_inc_ref(v_trace_2025_);
lean_inc_ref(v_log_2022_);
lean_del_object(v___x_2034_);
lean_dec(v_a_2021_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2070_ = lean_ctor_get(v_a_2020_, 2);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_a_2020_, 1);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_a_2020_, 0);
lean_dec(v_unused_2072_);
v___x_2059_ = v_a_2020_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_a_2020_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_a_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_a_2061_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2062_ = lean_io_error_to_string(v_a_2061_);
v___x_2063_ = 3;
v___x_2064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*1, v___x_2063_);
v___x_2065_ = lean_array_push(v_log_2022_, v___x_2064_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2065_);
v___x_2067_ = v___x_2059_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_trace_2025_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_buildTime_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3, v_action_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3 + 1, v_wantsRebuild_2024_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_a_2015_ = v___x_2028_;
v_a_2016_ = v___x_2067_;
goto v___jp_2014_;
}
}
}
}
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2086_; 
lean_inc(v_buildTime_2026_);
lean_inc_ref(v_trace_2025_);
lean_inc_ref(v_log_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v___x_2009_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2087_ = lean_ctor_get(v_a_2020_, 2);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_a_2020_, 1);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_a_2020_, 0);
lean_dec(v_unused_2089_);
v___x_2076_ = v_a_2020_;
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_a_2020_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_a_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v_a_2078_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2079_ = lean_io_error_to_string(v_a_2078_);
v___x_2080_ = 3;
v___x_2081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*1, v___x_2080_);
v___x_2082_ = lean_array_push(v_log_2022_, v___x_2081_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2082_);
v___x_2084_ = v___x_2076_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_trace_2025_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_buildTime_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3, v_action_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3 + 1, v_wantsRebuild_2024_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_a_2015_ = v___x_2028_;
v_a_2016_ = v___x_2084_;
goto v___jp_2014_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v_a_2091_; 
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_log_1998_);
lean_dec_ref(v_traceFile_1972_);
lean_dec_ref(v_inst_1970_);
v_a_2090_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2090_);
v_a_2091_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2013_, 2);
v_a_2015_ = v_a_2090_;
v_a_2016_ = v_a_2091_;
goto v___jp_2014_;
}
v___jp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_a_2019_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Lake_buildAction___redArg___lam__0(v___x_2010_, v___x_2017_, v_a_2016_);
lean_dec(v___x_2010_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v_a_1983_ = v_a_2015_;
v_a_1984_ = v_a_2019_;
goto v___jp_1982_;
}
}
}
else
{
uint8_t v___x_2093_; 
lean_dec_ref(v_a_1975_);
lean_dec_ref(v_build_1973_);
lean_dec_ref(v_inst_1970_);
v___x_2093_ = l_System_FilePath_pathExists(v_traceFile_1972_);
lean_dec_ref(v_traceFile_1972_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v___x_2009_);
lean_del_object(v___x_2004_);
v_log_1987_ = v_log_1998_;
v_action_1988_ = v___x_2007_;
v_wantsRebuild_1989_ = v_noBuild_2006_;
v_trace_1990_ = v_trace_2001_;
v_buildTime_1991_ = v_buildTime_2002_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2096_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1971_, v___x_2094_, v___x_2095_);
v___x_2097_ = l_Lake_BuildMetadata_writeFile(v___x_2009_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_dec_ref_known(v___x_2097_, 1);
lean_del_object(v___x_2004_);
v_log_1987_ = v_log_1998_;
v_action_1988_ = v___x_2007_;
v_wantsRebuild_1989_ = v_noBuild_2006_;
v_trace_1990_ = v_trace_2001_;
v_buildTime_1991_ = v_buildTime_2002_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = lean_io_error_to_string(v_a_2098_);
v___x_2100_ = 3;
v___x_2101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*1, v___x_2100_);
v___x_2102_ = lean_array_get_size(v_log_1998_);
v___x_2103_ = lean_array_push(v_log_1998_, v___x_2101_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2103_);
v___x_2105_ = v___x_2004_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_trace_2001_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_buildTime_2002_);
v___x_2105_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; 
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*3, v___x_2007_);
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*3 + 1, v_noBuild_2006_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2102_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
return v___x_2106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2109_, lean_object* v_depTrace_2110_, lean_object* v_traceFile_2111_, lean_object* v_build_2112_, lean_object* v_action_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_action_boxed_2121_; lean_object* v_res_2122_; 
v_action_boxed_2121_ = lean_unbox(v_action_2113_);
v_res_2122_ = l_Lake_buildAction___redArg(v_inst_2109_, v_depTrace_2110_, v_traceFile_2111_, v_build_2112_, v_action_boxed_2121_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_depTrace_2110_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2123_, lean_object* v_inst_2124_, lean_object* v_depTrace_2125_, lean_object* v_traceFile_2126_, lean_object* v_build_2127_, uint8_t v_action_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lake_buildAction___redArg(v_inst_2124_, v_depTrace_2125_, v_traceFile_2126_, v_build_2127_, v_action_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2137_, lean_object* v_inst_2138_, lean_object* v_depTrace_2139_, lean_object* v_traceFile_2140_, lean_object* v_build_2141_, lean_object* v_action_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
uint8_t v_action_boxed_2150_; lean_object* v_res_2151_; 
v_action_boxed_2150_ = lean_unbox(v_action_2142_);
v_res_2151_ = l_Lake_buildAction(v_00_u03b1_2137_, v_inst_2138_, v_depTrace_2139_, v_traceFile_2140_, v_build_2141_, v_action_boxed_2150_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_depTrace_2139_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_info_2154_, lean_object* v_depTrace_2155_, lean_object* v_traceFile_2156_, lean_object* v_build_2157_, uint8_t v_action_2158_, lean_object* v_oldTrace_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_log_2167_; uint8_t v_action_2168_; uint8_t v_wantsRebuild_2169_; lean_object* v_trace_2170_; lean_object* v_buildTime_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2239_; 
v_log_2167_ = lean_ctor_get(v_a_2165_, 0);
v_action_2168_ = lean_ctor_get_uint8(v_a_2165_, sizeof(void*)*3);
v_wantsRebuild_2169_ = lean_ctor_get_uint8(v_a_2165_, sizeof(void*)*3 + 1);
v_trace_2170_ = lean_ctor_get(v_a_2165_, 1);
v_buildTime_2171_ = lean_ctor_get(v_a_2165_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2173_ = v_a_2165_;
v_isShared_2174_ = v_isSharedCheck_2239_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_buildTime_2171_);
lean_inc(v_trace_2170_);
lean_inc(v_log_2167_);
lean_dec(v_a_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2239_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; 
lean_inc_ref(v_traceFile_2156_);
v___x_2175_ = l_Lake_readTraceFile(v_traceFile_2156_, v_log_2167_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2175_, 2);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v_a_2177_);
v___x_2179_ = v___x_2173_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2177_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*3, v_action_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2179_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2152_, v_inst_2153_, v_info_2154_, v_depTrace_2155_, v_a_2176_, v_oldTrace_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v___x_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2216_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_a_2182_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2184_ = v___x_2180_;
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
uint8_t v___x_2186_; uint8_t v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = 0;
v___x_2187_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
v___x_2188_ = l_Lake_instDecidableEqOutputStatus(v___x_2187_, v___x_2186_);
if (v___x_2188_ == 0)
{
uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
v___x_2189_ = 1;
v___x_2190_ = lean_box(v___x_2189_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2190_);
v___x_2192_ = v___x_2184_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2182_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___f_2194_; lean_object* v___x_2195_; 
lean_del_object(v___x_2184_);
v___f_2194_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2195_ = l_Lake_buildAction___redArg(v___f_2194_, v_depTrace_2155_, v_traceFile_2156_, v_build_2157_, v_action_2158_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2182_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2205_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2195_, 0);
lean_dec(v_unused_2206_);
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = 0;
v___x_2201_ = lean_box(v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_a_2196_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2195_, 0);
v_a_2208_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2195_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_inc(v_a_2207_);
lean_dec(v___x_2195_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2207_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_a_2208_);
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
else
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
v_a_2217_ = lean_ctor_get(v___x_2180_, 0);
v_a_2218_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2180_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2180_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2217_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
lean_dec(v_info_2154_);
lean_dec_ref(v_inst_2153_);
lean_dec_ref(v_inst_2152_);
v_a_2227_ = lean_ctor_get(v___x_2175_, 0);
v_a_2228_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2230_ = v___x_2175_;
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_inc(v_a_2227_);
lean_dec(v___x_2175_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v_a_2228_);
v___x_2233_ = v___x_2173_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2228_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*3, v_action_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2227_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_info_2242_, lean_object* v_depTrace_2243_, lean_object* v_traceFile_2244_, lean_object* v_build_2245_, lean_object* v_action_2246_, lean_object* v_oldTrace_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
uint8_t v_action_boxed_2255_; lean_object* v_res_2256_; 
v_action_boxed_2255_ = lean_unbox(v_action_2246_);
v_res_2256_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2240_, v_inst_2241_, v_info_2242_, v_depTrace_2243_, v_traceFile_2244_, v_build_2245_, v_action_boxed_2255_, v_oldTrace_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_oldTrace_2247_);
lean_dec_ref(v_depTrace_2243_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_info_2260_, lean_object* v_depTrace_2261_, lean_object* v_traceFile_2262_, lean_object* v_build_2263_, uint8_t v_action_2264_, lean_object* v_oldTrace_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_log_2273_; uint8_t v_action_2274_; uint8_t v_wantsRebuild_2275_; lean_object* v_trace_2276_; lean_object* v_buildTime_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2345_; 
v_log_2273_ = lean_ctor_get(v_a_2271_, 0);
v_action_2274_ = lean_ctor_get_uint8(v_a_2271_, sizeof(void*)*3);
v_wantsRebuild_2275_ = lean_ctor_get_uint8(v_a_2271_, sizeof(void*)*3 + 1);
v_trace_2276_ = lean_ctor_get(v_a_2271_, 1);
v_buildTime_2277_ = lean_ctor_get(v_a_2271_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2279_ = v_a_2271_;
v_isShared_2280_ = v_isSharedCheck_2345_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_buildTime_2277_);
lean_inc(v_trace_2276_);
lean_inc(v_log_2273_);
lean_dec(v_a_2271_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2345_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
lean_inc_ref(v_traceFile_2262_);
v___x_2281_ = l_Lake_readTraceFile(v_traceFile_2262_, v_log_2273_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
v_a_2283_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2281_, 2);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_a_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2283_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_trace_2276_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_buildTime_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3, v_action_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 1, v_wantsRebuild_2275_);
v___x_2285_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2258_, v_inst_2259_, v_info_2260_, v_depTrace_2261_, v_a_2282_, v_oldTrace_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2322_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_a_2288_ = lean_ctor_get(v___x_2286_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2290_ = v___x_2286_;
v_isShared_2291_ = v_isSharedCheck_2322_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2322_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint8_t v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2292_ = 0;
v___x_2293_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
v___x_2294_ = l_Lake_instDecidableEqOutputStatus(v___x_2293_, v___x_2292_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
v___x_2295_ = 1;
v___x_2296_ = lean_box(v___x_2295_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2296_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2288_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v___f_2300_; lean_object* v___x_2301_; 
lean_del_object(v___x_2290_);
v___f_2300_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2301_ = l_Lake_buildAction___redArg(v___f_2300_, v_depTrace_2261_, v_traceFile_2262_, v_build_2263_, v_action_2264_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2288_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2312_);
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = 0;
v___x_2307_ = lean_box(v___x_2306_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_a_2302_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2301_, 0);
v_a_2314_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2301_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2301_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
v_a_2323_ = lean_ctor_get(v___x_2286_, 0);
v_a_2324_ = lean_ctor_get(v___x_2286_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2286_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_inc(v_a_2323_);
lean_dec(v___x_2286_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2323_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
lean_dec(v_info_2260_);
lean_dec_ref(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
v_a_2333_ = lean_ctor_get(v___x_2281_, 0);
v_a_2334_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2336_ = v___x_2281_;
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_inc(v_a_2333_);
lean_dec(v___x_2281_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_a_2334_);
v___x_2339_ = v___x_2279_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2334_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_trace_2276_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_buildTime_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*3, v_action_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*3 + 1, v_wantsRebuild_2275_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2333_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_info_2349_, lean_object* v_depTrace_2350_, lean_object* v_traceFile_2351_, lean_object* v_build_2352_, lean_object* v_action_2353_, lean_object* v_oldTrace_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
uint8_t v_action_boxed_2362_; lean_object* v_res_2363_; 
v_action_boxed_2362_ = lean_unbox(v_action_2353_);
v_res_2363_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2346_, v_inst_2347_, v_inst_2348_, v_info_2349_, v_depTrace_2350_, v_traceFile_2351_, v_build_2352_, v_action_boxed_2362_, v_oldTrace_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_oldTrace_2354_);
lean_dec_ref(v_depTrace_2350_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_info_2366_, lean_object* v_depTrace_2367_, lean_object* v_traceFile_2368_, lean_object* v_build_2369_, uint8_t v_action_2370_, lean_object* v_oldTrace_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v_log_2383_; uint8_t v_action_2384_; uint8_t v_wantsRebuild_2385_; lean_object* v_trace_2386_; lean_object* v_buildTime_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2425_; 
v_log_2383_ = lean_ctor_get(v_a_2377_, 0);
v_action_2384_ = lean_ctor_get_uint8(v_a_2377_, sizeof(void*)*3);
v_wantsRebuild_2385_ = lean_ctor_get_uint8(v_a_2377_, sizeof(void*)*3 + 1);
v_trace_2386_ = lean_ctor_get(v_a_2377_, 1);
v_buildTime_2387_ = lean_ctor_get(v_a_2377_, 2);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2389_ = v_a_2377_;
v_isShared_2390_ = v_isSharedCheck_2425_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_buildTime_2387_);
lean_inc(v_trace_2386_);
lean_inc(v_log_2383_);
lean_dec(v_a_2377_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2425_;
goto v_resetjp_2388_;
}
v___jp_2379_:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_a_2380_);
lean_ctor_set(v___x_2382_, 1, v_a_2381_);
return v___x_2382_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_traceFile_2368_);
v___x_2391_ = l_Lake_readTraceFile(v_traceFile_2368_, v_log_2383_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
v_a_2393_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2391_, 2);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2393_);
v___x_2395_ = v___x_2389_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2393_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_trace_2386_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_buildTime_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3, v_action_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3 + 1, v_wantsRebuild_2385_);
v___x_2395_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2364_, v_inst_2365_, v_info_2366_, v_depTrace_2367_, v_a_2392_, v_oldTrace_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2416_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_a_2398_ = lean_ctor_get(v___x_2396_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v_a_2404_; uint8_t v___x_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2402_ = lean_box(0);
v___x_2408_ = 0;
v___x_2409_ = lean_unbox(v_a_2397_);
lean_dec(v_a_2397_);
v___x_2410_ = l_Lake_instDecidableEqOutputStatus(v___x_2409_, v___x_2408_);
if (v___x_2410_ == 0)
{
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
v_a_2404_ = v_a_2398_;
goto v___jp_2403_;
}
else
{
lean_object* v___f_2411_; lean_object* v___x_2412_; 
v___f_2411_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2412_ = l_Lake_buildAction___redArg(v___f_2411_, v_depTrace_2367_, v_traceFile_2368_, v_build_2369_, v_action_2370_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2398_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 2);
v_a_2404_ = v_a_2413_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2414_; lean_object* v_a_2415_; 
lean_del_object(v___x_2400_);
v_a_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2414_);
v_a_2415_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2412_, 2);
v_a_2380_ = v_a_2414_;
v_a_2381_ = v_a_2415_;
goto v___jp_2379_;
}
}
v___jp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v_a_2404_);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2406_ = v___x_2400_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_a_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v_a_2418_; 
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
v_a_2417_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2417_);
v_a_2418_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2396_, 2);
v_a_2380_ = v_a_2417_;
v_a_2381_ = v_a_2418_;
goto v___jp_2379_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v_a_2421_; lean_object* v___x_2423_; 
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
lean_dec(v_info_2366_);
lean_dec_ref(v_inst_2365_);
lean_dec_ref(v_inst_2364_);
v_a_2420_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2420_);
v_a_2421_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2391_, 2);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2421_);
v___x_2423_ = v___x_2389_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_trace_2386_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_buildTime_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*3, v_action_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*3 + 1, v_wantsRebuild_2385_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
v_a_2380_ = v_a_2420_;
v_a_2381_ = v___x_2423_;
goto v___jp_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_info_2428_, lean_object* v_depTrace_2429_, lean_object* v_traceFile_2430_, lean_object* v_build_2431_, lean_object* v_action_2432_, lean_object* v_oldTrace_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
uint8_t v_action_boxed_2441_; lean_object* v_res_2442_; 
v_action_boxed_2441_ = lean_unbox(v_action_2432_);
v_res_2442_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2426_, v_inst_2427_, v_info_2428_, v_depTrace_2429_, v_traceFile_2430_, v_build_2431_, v_action_boxed_2441_, v_oldTrace_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_oldTrace_2433_);
lean_dec_ref(v_depTrace_2429_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_info_2446_, lean_object* v_depTrace_2447_, lean_object* v_traceFile_2448_, lean_object* v_build_2449_, uint8_t v_action_2450_, lean_object* v_oldTrace_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_a_2460_; lean_object* v_a_2461_; lean_object* v_log_2463_; uint8_t v_action_2464_; uint8_t v_wantsRebuild_2465_; lean_object* v_trace_2466_; lean_object* v_buildTime_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2505_; 
v_log_2463_ = lean_ctor_get(v_a_2457_, 0);
v_action_2464_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*3);
v_wantsRebuild_2465_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*3 + 1);
v_trace_2466_ = lean_ctor_get(v_a_2457_, 1);
v_buildTime_2467_ = lean_ctor_get(v_a_2457_, 2);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2469_ = v_a_2457_;
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_buildTime_2467_);
lean_inc(v_trace_2466_);
lean_inc(v_log_2463_);
lean_dec(v_a_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
v___jp_2459_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2460_);
lean_ctor_set(v___x_2462_, 1, v_a_2461_);
return v___x_2462_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; 
lean_inc_ref(v_traceFile_2448_);
v___x_2471_ = l_Lake_readTraceFile(v_traceFile_2448_, v_log_2463_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v_a_2473_; lean_object* v___x_2475_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
v_a_2473_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2471_, 2);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_a_2473_);
v___x_2475_ = v___x_2469_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2473_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_trace_2466_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_buildTime_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3, v_action_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3 + 1, v_wantsRebuild_2465_);
v___x_2475_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2444_, v_inst_2445_, v_info_2446_, v_depTrace_2447_, v_a_2472_, v_oldTrace_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2496_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v_a_2484_; uint8_t v___x_2488_; uint8_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2482_ = lean_box(0);
v___x_2488_ = 0;
v___x_2489_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
v___x_2490_ = l_Lake_instDecidableEqOutputStatus(v___x_2489_, v___x_2488_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
v_a_2484_ = v_a_2478_;
goto v___jp_2483_;
}
else
{
lean_object* v___f_2491_; lean_object* v___x_2492_; 
v___f_2491_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2492_ = l_Lake_buildAction___redArg(v___f_2491_, v_depTrace_2447_, v_traceFile_2448_, v_build_2449_, v_action_2450_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2478_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 2);
v_a_2484_ = v_a_2493_;
goto v___jp_2483_;
}
else
{
lean_object* v_a_2494_; lean_object* v_a_2495_; 
lean_del_object(v___x_2480_);
v_a_2494_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2494_);
v_a_2495_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2492_, 2);
v_a_2460_ = v_a_2494_;
v_a_2461_ = v_a_2495_;
goto v___jp_2459_;
}
}
v___jp_2483_:
{
lean_object* v___x_2486_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_a_2484_);
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2486_ = v___x_2480_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v_a_2498_; 
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
v_a_2497_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2497_);
v_a_2498_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2476_, 2);
v_a_2460_ = v_a_2497_;
v_a_2461_ = v_a_2498_;
goto v___jp_2459_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v_a_2501_; lean_object* v___x_2503_; 
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
lean_dec(v_info_2446_);
lean_dec_ref(v_inst_2445_);
lean_dec_ref(v_inst_2444_);
v_a_2500_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2500_);
v_a_2501_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2471_, 2);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_a_2501_);
v___x_2503_ = v___x_2469_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2501_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_trace_2466_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_buildTime_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*3, v_action_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*3 + 1, v_wantsRebuild_2465_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
v_a_2460_ = v_a_2500_;
v_a_2461_ = v___x_2503_;
goto v___jp_2459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_info_2509_, lean_object* v_depTrace_2510_, lean_object* v_traceFile_2511_, lean_object* v_build_2512_, lean_object* v_action_2513_, lean_object* v_oldTrace_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_action_boxed_2522_; lean_object* v_res_2523_; 
v_action_boxed_2522_ = lean_unbox(v_action_2513_);
v_res_2523_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2506_, v_inst_2507_, v_inst_2508_, v_info_2509_, v_depTrace_2510_, v_traceFile_2511_, v_build_2512_, v_action_boxed_2522_, v_oldTrace_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_oldTrace_2514_);
lean_dec_ref(v_depTrace_2510_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2525_, uint64_t v_hash_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v_hashFile_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2529_ = lean_string_append(v_file_2525_, v___x_2528_);
lean_inc_ref(v_hashFile_2529_);
v___x_2530_ = l_Lake_createParentDirs(v_hashFile_2529_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref_known(v___x_2530_, 1);
v___x_2531_ = l_Lake_lowerHexUInt64(v_hash_2526_);
v___x_2532_ = l_IO_FS_writeFile(v_hashFile_2529_, v___x_2531_);
lean_dec_ref(v___x_2531_);
lean_dec_ref(v_hashFile_2529_);
return v___x_2532_;
}
else
{
lean_dec_ref(v_hashFile_2529_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2533_, lean_object* v_hash_2534_, lean_object* v_a_2535_){
_start:
{
uint64_t v_hash_boxed_2536_; lean_object* v_res_2537_; 
v_hash_boxed_2536_ = lean_unbox_uint64(v_hash_2534_);
lean_dec_ref(v_hash_2534_);
v_res_2537_ = l_Lake_writeFileHash(v_file_2533_, v_hash_boxed_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2538_, uint8_t v_text_2539_){
_start:
{
lean_object* v___y_2542_; 
if (v_text_2539_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lake_computeBinFileHash(v_file_2538_);
v___y_2542_ = v___x_2554_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lake_computeTextFileHash(v_file_2538_);
v___y_2542_ = v___x_2555_;
goto v___jp_2541_;
}
v___jp_2541_:
{
if (lean_obj_tag(v___y_2542_) == 0)
{
lean_object* v_a_2543_; uint64_t v___x_2544_; lean_object* v___x_2545_; 
v_a_2543_ = lean_ctor_get(v___y_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___y_2542_, 1);
v___x_2544_ = lean_unbox_uint64(v_a_2543_);
lean_dec(v_a_2543_);
v___x_2545_ = l_Lake_writeFileHash(v_file_2538_, v___x_2544_);
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_file_2538_);
v_a_2546_ = lean_ctor_get(v___y_2542_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___y_2542_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___y_2542_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___y_2542_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2556_, lean_object* v_text_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v_text_boxed_2559_; lean_object* v_res_2560_; 
v_text_boxed_2559_ = lean_unbox(v_text_2557_);
v_res_2560_ = l_Lake_cacheFileHash(v_file_2556_, v_text_boxed_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2564_ = lean_string_append(v_file_2561_, v___x_2563_);
v___x_2565_ = l_Lake_removeFileIfExists(v___x_2564_);
lean_dec_ref(v___x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lake_clearFileHash(v_file_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2569_, uint8_t v_text_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_toBuildConfig_2574_; uint8_t v_trustHash_2575_; lean_object* v___x_2576_; lean_object* v_hashFile_2577_; uint8_t v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2617_; 
v_toBuildConfig_2574_ = lean_ctor_get(v_a_2571_, 0);
v_trustHash_2575_ = lean_ctor_get_uint8(v_toBuildConfig_2574_, sizeof(void*)*3 + 1);
v___x_2576_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2569_);
v_hashFile_2577_ = lean_string_append(v_file_2569_, v___x_2576_);
if (v_trustHash_2575_ == 0)
{
v___y_2617_ = v_a_2572_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lake_Hash_load_x3f(v_hashFile_2577_);
if (lean_obj_tag(v___x_2630_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_hashFile_2577_);
lean_dec_ref(v_file_2569_);
v_val_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_val_2631_);
lean_ctor_set(v___x_2632_, 1, v_a_2572_);
return v___x_2632_;
}
else
{
lean_dec(v___x_2630_);
v___y_2617_ = v_a_2572_;
goto v___jp_2616_;
}
}
v___jp_2578_:
{
if (lean_obj_tag(v___y_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___y_2584_, 1);
lean_inc_ref(v_hashFile_2577_);
v___x_2586_ = l_Lake_createParentDirs(v_hashFile_2577_);
if (lean_obj_tag(v___x_2586_) == 0)
{
uint64_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref_known(v___x_2586_, 1);
v___x_2587_ = lean_unbox_uint64(v_a_2585_);
v___x_2588_ = l_Lake_lowerHexUInt64(v___x_2587_);
v___x_2589_ = l_IO_FS_writeFile(v_hashFile_2577_, v___x_2588_);
lean_dec_ref(v___x_2588_);
lean_dec_ref(v_hashFile_2577_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref_known(v___x_2589_, 1);
v___x_2590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2590_, 0, v___y_2583_);
lean_ctor_set(v___x_2590_, 1, v___y_2582_);
lean_ctor_set(v___x_2590_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2585_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
return v___x_2591_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec(v_a_2585_);
v_a_2592_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2593_ = lean_io_error_to_string(v_a_2592_);
v___x_2594_ = 3;
v___x_2595_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*1, v___x_2594_);
v___x_2596_ = lean_array_get_size(v___y_2583_);
v___x_2597_ = lean_array_push(v___y_2583_, v___x_2595_);
v___x_2598_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___y_2582_);
lean_ctor_set(v___x_2598_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
return v___x_2599_;
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_a_2585_);
lean_dec_ref(v_hashFile_2577_);
v_a_2600_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2601_ = lean_io_error_to_string(v_a_2600_);
v___x_2602_ = 3;
v___x_2603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*1, v___x_2602_);
v___x_2604_ = lean_array_get_size(v___y_2583_);
v___x_2605_ = lean_array_push(v___y_2583_, v___x_2603_);
v___x_2606_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___y_2582_);
lean_ctor_set(v___x_2606_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2604_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
return v___x_2607_;
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_hashFile_2577_);
v_a_2608_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___y_2584_, 1);
v___x_2609_ = lean_io_error_to_string(v_a_2608_);
v___x_2610_ = 3;
v___x_2611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*1, v___x_2610_);
v___x_2612_ = lean_array_get_size(v___y_2583_);
v___x_2613_ = lean_array_push(v___y_2583_, v___x_2611_);
v___x_2614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___y_2582_);
lean_ctor_set(v___x_2614_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2612_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
return v___x_2615_;
}
}
v___jp_2616_:
{
if (v_text_2570_ == 0)
{
lean_object* v_log_2618_; uint8_t v_action_2619_; uint8_t v_wantsRebuild_2620_; lean_object* v_trace_2621_; lean_object* v_buildTime_2622_; lean_object* v___x_2623_; 
v_log_2618_ = lean_ctor_get(v___y_2617_, 0);
lean_inc_ref(v_log_2618_);
v_action_2619_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3);
v_wantsRebuild_2620_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3 + 1);
v_trace_2621_ = lean_ctor_get(v___y_2617_, 1);
lean_inc_ref(v_trace_2621_);
v_buildTime_2622_ = lean_ctor_get(v___y_2617_, 2);
lean_inc(v_buildTime_2622_);
lean_dec_ref(v___y_2617_);
v___x_2623_ = l_Lake_computeBinFileHash(v_file_2569_);
lean_dec_ref(v_file_2569_);
v___y_2579_ = v_action_2619_;
v___y_2580_ = v_buildTime_2622_;
v___y_2581_ = v_wantsRebuild_2620_;
v___y_2582_ = v_trace_2621_;
v___y_2583_ = v_log_2618_;
v___y_2584_ = v___x_2623_;
goto v___jp_2578_;
}
else
{
lean_object* v_log_2624_; uint8_t v_action_2625_; uint8_t v_wantsRebuild_2626_; lean_object* v_trace_2627_; lean_object* v_buildTime_2628_; lean_object* v___x_2629_; 
v_log_2624_ = lean_ctor_get(v___y_2617_, 0);
lean_inc_ref(v_log_2624_);
v_action_2625_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3);
v_wantsRebuild_2626_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3 + 1);
v_trace_2627_ = lean_ctor_get(v___y_2617_, 1);
lean_inc_ref(v_trace_2627_);
v_buildTime_2628_ = lean_ctor_get(v___y_2617_, 2);
lean_inc(v_buildTime_2628_);
lean_dec_ref(v___y_2617_);
v___x_2629_ = l_Lake_computeTextFileHash(v_file_2569_);
lean_dec_ref(v_file_2569_);
v___y_2579_ = v_action_2625_;
v___y_2580_ = v_buildTime_2628_;
v___y_2581_ = v_wantsRebuild_2626_;
v___y_2582_ = v_trace_2627_;
v___y_2583_ = v_log_2624_;
v___y_2584_ = v___x_2629_;
goto v___jp_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2633_, lean_object* v_text_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_text_boxed_2638_; lean_object* v_res_2639_; 
v_text_boxed_2638_ = lean_unbox(v_text_2634_);
v_res_2639_ = l_Lake_fetchFileHash___redArg(v_file_2633_, v_text_boxed_2638_, v_a_2635_, v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2640_, uint8_t v_text_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lake_fetchFileHash___redArg(v_file_2640_, v_text_2641_, v_a_2646_, v_a_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2650_, lean_object* v_text_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_text_boxed_2659_; lean_object* v_res_2660_; 
v_text_boxed_2659_ = lean_unbox(v_text_2651_);
v_res_2660_ = l_Lake_fetchFileHash(v_file_2650_, v_text_boxed_2659_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2661_, uint8_t v_text_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; 
lean_inc_ref(v_file_2661_);
v___x_2666_ = l_Lake_fetchFileHash___redArg(v_file_2661_, v_text_2662_, v_a_2663_, v_a_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2705_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 1);
v_a_2668_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2667_);
lean_inc(v_a_2668_);
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_log_2672_; uint8_t v_action_2673_; uint8_t v_wantsRebuild_2674_; lean_object* v_trace_2675_; lean_object* v_buildTime_2676_; lean_object* v___x_2677_; 
v_log_2672_ = lean_ctor_get(v_a_2667_, 0);
v_action_2673_ = lean_ctor_get_uint8(v_a_2667_, sizeof(void*)*3);
v_wantsRebuild_2674_ = lean_ctor_get_uint8(v_a_2667_, sizeof(void*)*3 + 1);
v_trace_2675_ = lean_ctor_get(v_a_2667_, 1);
v_buildTime_2676_ = lean_ctor_get(v_a_2667_, 2);
v___x_2677_ = lean_io_metadata(v_file_2661_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v_modified_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint64_t v___x_2682_; lean_object* v___x_2684_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v_modified_2679_ = lean_ctor_get(v_a_2678_, 1);
lean_inc_ref(v_modified_2679_);
lean_dec(v_a_2678_);
v___x_2680_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2681_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2681_, 0, v_file_2661_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_ctor_set(v___x_2681_, 2, v_modified_2679_);
v___x_2682_ = lean_unbox_uint64(v_a_2668_);
lean_dec(v_a_2668_);
lean_ctor_set_uint64(v___x_2681_, sizeof(void*)*3, v___x_2682_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2681_);
v___x_2684_ = v___x_2670_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_a_2667_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_buildTime_2676_);
lean_inc_ref(v_trace_2675_);
lean_inc_ref(v_log_2672_);
lean_dec(v_a_2668_);
lean_dec_ref(v_file_2661_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2667_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; 
v_unused_2702_ = lean_ctor_get(v_a_2667_, 2);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_a_2667_, 1);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_a_2667_, 0);
lean_dec(v_unused_2704_);
v___x_2687_ = v_a_2667_;
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v_a_2667_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_a_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2690_ = lean_io_error_to_string(v_a_2689_);
v___x_2691_ = 3;
v___x_2692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*1, v___x_2691_);
v___x_2693_ = lean_array_get_size(v_log_2672_);
v___x_2694_ = lean_array_push(v_log_2672_, v___x_2692_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2694_);
v___x_2696_ = v___x_2687_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_trace_2675_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_buildTime_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*3, v_action_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*3 + 1, v_wantsRebuild_2674_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 1);
lean_ctor_set(v___x_2670_, 1, v___x_2696_);
lean_ctor_set(v___x_2670_, 0, v___x_2693_);
v___x_2698_ = v___x_2670_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v_file_2661_);
v_a_2706_ = lean_ctor_get(v___x_2666_, 0);
v_a_2707_ = lean_ctor_get(v___x_2666_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2666_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_inc(v_a_2706_);
lean_dec(v___x_2666_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2706_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2715_, lean_object* v_text_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_text_boxed_2720_; lean_object* v_res_2721_; 
v_text_boxed_2720_ = lean_unbox(v_text_2716_);
v_res_2721_ = l_Lake_fetchFileTrace___redArg(v_file_2715_, v_text_boxed_2720_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2722_, uint8_t v_text_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lake_fetchFileTrace___redArg(v_file_2722_, v_text_2723_, v_a_2728_, v_a_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2732_, lean_object* v_text_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
uint8_t v_text_boxed_2741_; lean_object* v_res_2742_; 
v_text_boxed_2741_ = lean_unbox(v_text_2733_);
v_res_2742_ = l_Lake_fetchFileTrace(v_file_2732_, v_text_boxed_2741_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2743_, lean_object* v_a_x3f_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_log_2748_; uint8_t v_action_2749_; uint8_t v_wantsRebuild_2750_; lean_object* v_trace_2751_; lean_object* v_buildTime_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2763_; 
v___x_2747_ = lean_io_mono_ms_now();
v_log_2748_ = lean_ctor_get(v___y_2745_, 0);
v_action_2749_ = lean_ctor_get_uint8(v___y_2745_, sizeof(void*)*3);
v_wantsRebuild_2750_ = lean_ctor_get_uint8(v___y_2745_, sizeof(void*)*3 + 1);
v_trace_2751_ = lean_ctor_get(v___y_2745_, 1);
v_buildTime_2752_ = lean_ctor_get(v___y_2745_, 2);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___y_2745_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2754_ = v___y_2745_;
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_buildTime_2752_);
lean_inc(v_trace_2751_);
lean_inc(v_log_2748_);
lean_dec(v___y_2745_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2756_ = lean_nat_sub(v___x_2747_, v_val_2743_);
lean_dec(v___x_2747_);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_nat_add(v_buildTime_2752_, v___x_2756_);
lean_dec(v___x_2756_);
lean_dec(v_buildTime_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 2, v___x_2758_);
v___x_2760_ = v___x_2754_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_log_2748_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_trace_2751_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v___x_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*3, v_action_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*3 + 1, v_wantsRebuild_2750_);
v___x_2760_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2757_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2764_, lean_object* v_a_x3f_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2764_, v_a_x3f_2765_, v___y_2766_);
lean_dec(v_a_x3f_2765_);
lean_dec(v_val_2764_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2769_, lean_object* v_file_2770_, lean_object* v_a_2771_, lean_object* v_depTrace_2772_, lean_object* v_traceFile_2773_, uint8_t v_action_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v_log_2786_; uint8_t v_action_2787_; uint8_t v_wantsRebuild_2788_; lean_object* v_trace_2789_; lean_object* v_buildTime_2790_; lean_object* v_toBuildConfig_2796_; lean_object* v_log_2797_; uint8_t v_action_2798_; uint8_t v_wantsRebuild_2799_; lean_object* v_trace_2800_; lean_object* v_buildTime_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2924_; 
v_toBuildConfig_2796_ = lean_ctor_get(v_a_2778_, 0);
v_log_2797_ = lean_ctor_get(v_a_2779_, 0);
v_action_2798_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*3);
v_wantsRebuild_2799_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*3 + 1);
v_trace_2800_ = lean_ctor_get(v_a_2779_, 1);
v_buildTime_2801_ = lean_ctor_get(v_a_2779_, 2);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2779_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2803_ = v_a_2779_;
v_isShared_2804_ = v_isSharedCheck_2924_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_buildTime_2801_);
lean_inc(v_trace_2800_);
lean_inc(v_log_2797_);
lean_dec(v_a_2779_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2924_;
goto v_resetjp_2802_;
}
v___jp_2781_:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_a_2782_);
lean_ctor_set(v___x_2784_, 1, v_a_2783_);
return v___x_2784_;
}
v___jp_2785_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2791_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2792_ = lean_array_get_size(v_log_2786_);
v___x_2793_ = lean_array_push(v_log_2786_, v___x_2791_);
v___x_2794_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_trace_2789_);
lean_ctor_set(v___x_2794_, 2, v_buildTime_2790_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3, v_action_2787_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3 + 1, v_wantsRebuild_2788_);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2792_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
return v___x_2795_;
}
v_resetjp_2802_:
{
uint8_t v_noBuild_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_noBuild_2805_ = lean_ctor_get_uint8(v_toBuildConfig_2796_, sizeof(void*)*3 + 2);
v___x_2806_ = l_Lake_JobAction_merge(v_action_2798_, v_action_2774_);
v___x_2807_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2773_);
v___x_2808_ = l_System_FilePath_addExtension(v_traceFile_2773_, v___x_2807_);
if (v_noBuild_2805_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2797_);
if (v_isShared_2804_ == 0)
{
v___x_2811_ = v___x_2803_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_log_2797_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_trace_2800_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_buildTime_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*3 + 1, v_wantsRebuild_2799_);
v___x_2811_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v_a_2814_; lean_object* v_a_2815_; 
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*3, v___x_2806_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc(v_a_2776_);
lean_inc(v_a_2775_);
v___x_2812_ = lean_apply_7(v_build_2769_, v_a_2771_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v___x_2811_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2819_; lean_object* v_log_2820_; uint8_t v_action_2821_; uint8_t v_wantsRebuild_2822_; lean_object* v_trace_2823_; lean_object* v_buildTime_2824_; lean_object* v___x_2825_; 
v_a_2819_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2812_, 2);
v_log_2820_ = lean_ctor_get(v_a_2819_, 0);
v_action_2821_ = lean_ctor_get_uint8(v_a_2819_, sizeof(void*)*3);
v_wantsRebuild_2822_ = lean_ctor_get_uint8(v_a_2819_, sizeof(void*)*3 + 1);
v_trace_2823_ = lean_ctor_get(v_a_2819_, 1);
v_buildTime_2824_ = lean_ctor_get(v_a_2819_, 2);
v___x_2825_ = l_Lake_clearFileHash(v_file_2770_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = lean_array_get_size(v_log_2797_);
lean_dec_ref(v_log_2797_);
v___x_2828_ = lean_array_get_size(v_log_2820_);
v___x_2829_ = l_Array_extract___redArg(v_log_2820_, v___x_2827_, v___x_2828_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2772_, v___x_2830_, v___x_2829_);
v___x_2832_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2773_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2873_; 
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2874_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2873_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2873_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lake_removeFileIfExists(v___x_2808_);
lean_dec_ref(v___x_2808_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2856_; 
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2857_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2856_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2856_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
lean_inc(v_a_2826_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v_a_2826_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2826_);
v___x_2841_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2841_);
v___x_2843_ = v___x_2834_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v___x_2844_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2809_, v___x_2843_, v_a_2819_);
lean_dec_ref(v___x_2843_);
lean_dec(v___x_2809_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2853_);
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_a_2826_);
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2826_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
else
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2869_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_del_object(v___x_2834_);
lean_dec(v_a_2826_);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; lean_object* v_unused_2871_; lean_object* v_unused_2872_; 
v_unused_2870_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2872_);
v___x_2859_ = v_a_2819_;
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v_a_2819_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_a_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v_a_2861_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2862_ = lean_io_error_to_string(v_a_2861_);
v___x_2863_ = 3;
v___x_2864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2863_);
v___x_2865_ = lean_array_push(v_log_2820_, v___x_2864_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2865_);
v___x_2867_ = v___x_2859_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
v_a_2814_ = v___x_2828_;
v_a_2815_ = v___x_2867_;
goto v___jp_2813_;
}
}
}
}
}
else
{
lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2886_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_dec(v_a_2826_);
lean_dec_ref(v___x_2808_);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2887_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2889_);
v___x_2876_ = v_a_2819_;
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
else
{
lean_dec(v_a_2819_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v_a_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v_a_2878_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2879_ = lean_io_error_to_string(v_a_2878_);
v___x_2880_ = 3;
v___x_2881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set_uint8(v___x_2881_, sizeof(void*)*1, v___x_2880_);
v___x_2882_ = lean_array_push(v_log_2820_, v___x_2881_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2882_);
v___x_2884_ = v___x_2876_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_a_2814_ = v___x_2828_;
v_a_2815_ = v___x_2884_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2902_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_log_2797_);
lean_dec_ref(v_traceFile_2773_);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2903_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2905_);
v___x_2891_ = v_a_2819_;
v_isShared_2892_ = v_isSharedCheck_2902_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v_a_2819_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2902_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_a_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2894_ = lean_io_error_to_string(v_a_2893_);
v___x_2895_ = 3;
v___x_2896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*1, v___x_2895_);
v___x_2897_ = lean_array_get_size(v_log_2820_);
v___x_2898_ = lean_array_push(v_log_2820_, v___x_2896_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2898_);
v___x_2900_ = v___x_2891_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
v_a_2814_ = v___x_2897_;
v_a_2815_ = v___x_2900_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v_a_2907_; 
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_log_2797_);
lean_dec_ref(v_traceFile_2773_);
lean_dec_ref(v_file_2770_);
v_a_2906_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2906_);
v_a_2907_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2812_, 2);
v_a_2814_ = v_a_2906_;
v_a_2815_ = v_a_2907_;
goto v___jp_2813_;
}
v___jp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v_a_2818_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2809_, v___x_2816_, v_a_2815_);
lean_dec(v___x_2809_);
v_a_2818_ = lean_ctor_get(v___x_2817_, 1);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v_a_2782_ = v_a_2814_;
v_a_2783_ = v_a_2818_;
goto v___jp_2781_;
}
}
}
else
{
uint8_t v___x_2909_; 
lean_dec_ref(v_a_2771_);
lean_dec_ref(v_file_2770_);
lean_dec_ref(v_build_2769_);
v___x_2909_ = l_System_FilePath_pathExists(v_traceFile_2773_);
lean_dec_ref(v_traceFile_2773_);
if (v___x_2909_ == 0)
{
lean_dec_ref(v___x_2808_);
lean_del_object(v___x_2803_);
v_log_2786_ = v_log_2797_;
v_action_2787_ = v___x_2806_;
v_wantsRebuild_2788_ = v_noBuild_2805_;
v_trace_2789_ = v_trace_2800_;
v_buildTime_2790_ = v_buildTime_2801_;
goto v___jp_2785_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_box(0);
v___x_2911_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2912_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2772_, v___x_2910_, v___x_2911_);
v___x_2913_ = l_Lake_BuildMetadata_writeFile(v___x_2808_, v___x_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
lean_del_object(v___x_2803_);
v_log_2786_ = v_log_2797_;
v_action_2787_ = v___x_2806_;
v_wantsRebuild_2788_ = v_noBuild_2805_;
v_trace_2789_ = v_trace_2800_;
v_buildTime_2790_ = v_buildTime_2801_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = lean_io_error_to_string(v_a_2914_);
v___x_2916_ = 3;
v___x_2917_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*1, v___x_2916_);
v___x_2918_ = lean_array_get_size(v_log_2797_);
v___x_2919_ = lean_array_push(v_log_2797_, v___x_2917_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2919_);
v___x_2921_ = v___x_2803_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_trace_2800_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_buildTime_2801_);
v___x_2921_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; 
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3, v___x_2806_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 1, v_noBuild_2805_);
v___x_2922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2918_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
return v___x_2922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2925_, lean_object* v_file_2926_, lean_object* v_a_2927_, lean_object* v_depTrace_2928_, lean_object* v_traceFile_2929_, lean_object* v_action_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
uint8_t v_action_boxed_2937_; lean_object* v_res_2938_; 
v_action_boxed_2937_ = lean_unbox(v_action_2930_);
v_res_2938_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2925_, v_file_2926_, v_a_2927_, v_depTrace_2928_, v_traceFile_2929_, v_action_boxed_2937_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_depTrace_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2939_, lean_object* v_self_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_io_metadata(v_info_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v_modified_2944_; uint8_t v___x_2945_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v_modified_2944_ = lean_ctor_get(v_a_2943_, 1);
lean_inc_ref(v_modified_2944_);
lean_dec(v_a_2943_);
v___x_2945_ = l_IO_FS_instOrdSystemTime_ord(v_self_2940_, v_modified_2944_);
lean_dec_ref(v_modified_2944_);
if (v___x_2945_ == 0)
{
uint8_t v___x_2946_; 
v___x_2946_ = 1;
return v___x_2946_;
}
else
{
uint8_t v___x_2947_; 
v___x_2947_ = 0;
return v___x_2947_;
}
}
else
{
uint8_t v___x_2948_; 
lean_dec_ref_known(v___x_2942_, 1);
v___x_2948_ = 0;
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2949_, lean_object* v_self_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_res_2952_; lean_object* v_r_2953_; 
v_res_2952_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2949_, v_self_2950_);
lean_dec_ref(v_self_2950_);
lean_dec_ref(v_info_2949_);
v_r_2953_ = lean_box(v_res_2952_);
return v_r_2953_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2954_) == 0)
{
if (lean_obj_tag(v_x_2955_) == 0)
{
uint8_t v___x_2956_; 
v___x_2956_ = 1;
return v___x_2956_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = 0;
return v___x_2957_;
}
}
else
{
if (lean_obj_tag(v_x_2955_) == 0)
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
else
{
lean_object* v_val_2959_; lean_object* v_val_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint8_t v___x_2963_; 
v_val_2959_ = lean_ctor_get(v_x_2954_, 0);
v_val_2960_ = lean_ctor_get(v_x_2955_, 0);
v___x_2961_ = lean_unbox_uint64(v_val_2959_);
v___x_2962_ = lean_unbox_uint64(v_val_2960_);
v___x_2963_ = lean_uint64_dec_eq(v___x_2961_, v___x_2962_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2964_, lean_object* v_x_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2964_, v_x_2965_);
lean_dec(v_x_2965_);
lean_dec(v_x_2964_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2968_, lean_object* v_depTrace_2969_, lean_object* v_depHash_2970_, lean_object* v_oldTrace_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
uint64_t v_hash_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_hash_2975_ = lean_ctor_get_uint64(v_depTrace_2969_, sizeof(void*)*3);
v___x_2976_ = lean_box_uint64(v_hash_2975_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___x_2978_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2977_, v_depHash_2970_);
lean_dec_ref_known(v___x_2977_, 1);
if (v___x_2978_ == 0)
{
lean_object* v_toBuildConfig_2979_; uint8_t v_oldMode_2980_; 
v_toBuildConfig_2979_ = lean_ctor_get(v_a_2972_, 0);
v_oldMode_2980_ = lean_ctor_get_uint8(v_toBuildConfig_2979_, sizeof(void*)*3);
if (v_oldMode_2980_ == 0)
{
uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = 0;
v___x_2982_ = lean_box(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v_a_2973_);
return v___x_2983_;
}
else
{
uint8_t v___x_2984_; 
v___x_2984_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2968_, v_oldTrace_2971_);
if (v___x_2984_ == 0)
{
uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = 0;
v___x_2986_ = lean_box(v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_a_2973_);
return v___x_2987_;
}
else
{
uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = 1;
v___x_2989_ = lean_box(v___x_2988_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v_a_2973_);
return v___x_2990_;
}
}
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = l_System_FilePath_pathExists(v_info_2968_);
if (v___x_2991_ == 0)
{
uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = 0;
v___x_2993_ = lean_box(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
lean_ctor_set(v___x_2994_, 1, v_a_2973_);
return v___x_2994_;
}
else
{
uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = 2;
v___x_2996_ = lean_box(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v_a_2973_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2998_, lean_object* v_depTrace_2999_, lean_object* v_depHash_3000_, lean_object* v_oldTrace_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2998_, v_depTrace_2999_, v_depHash_3000_, v_oldTrace_3001_, v_a_3002_, v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec_ref(v_oldTrace_3001_);
lean_dec(v_depHash_3000_);
lean_dec_ref(v_depTrace_2999_);
lean_dec_ref(v_info_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_3006_, lean_object* v_info_3007_, lean_object* v_depTrace_3008_, lean_object* v_savedTrace_3009_, lean_object* v_oldTrace_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
if (lean_obj_tag(v_savedTrace_3009_) == 2)
{
lean_object* v_data_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3067_; 
v_data_3017_ = lean_ctor_get(v_savedTrace_3009_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_savedTrace_3009_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3019_ = v_savedTrace_3009_;
v_isShared_3020_ = v_isSharedCheck_3067_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_data_3017_);
lean_dec(v_savedTrace_3009_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3067_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint64_t v_depHash_3021_; lean_object* v_log_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v_depHash_3021_ = lean_ctor_get_uint64(v_data_3017_, sizeof(void*)*3);
v_log_3022_ = lean_ctor_get(v_data_3017_, 2);
lean_inc_ref(v_log_3022_);
lean_dec_ref(v_data_3017_);
v___x_3023_ = lean_box_uint64(v_depHash_3021_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3023_);
v___x_3025_ = v___x_3019_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v_a_3027_; lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3065_; 
v___x_3026_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3007_, v_depTrace_3008_, v___x_3025_, v_oldTrace_3010_, v_a_3014_, v_a_3015_);
lean_dec_ref(v___x_3025_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_a_3028_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3030_ = v___x_3026_;
v_isShared_3031_ = v_isSharedCheck_3065_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3065_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___y_3033_; uint8_t v___x_3037_; uint8_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3037_ = 0;
v___x_3038_ = lean_unbox(v_a_3027_);
v___x_3039_ = l_Lake_instDecidableEqOutputStatus(v___x_3038_, v___x_3037_);
if (v___x_3039_ == 0)
{
lean_object* v_log_3040_; uint8_t v_action_3041_; uint8_t v_wantsRebuild_3042_; lean_object* v_trace_3043_; lean_object* v_buildTime_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3064_; 
v_log_3040_ = lean_ctor_get(v_a_3028_, 0);
v_action_3041_ = lean_ctor_get_uint8(v_a_3028_, sizeof(void*)*3);
v_wantsRebuild_3042_ = lean_ctor_get_uint8(v_a_3028_, sizeof(void*)*3 + 1);
v_trace_3043_ = lean_ctor_get(v_a_3028_, 1);
v_buildTime_3044_ = lean_ctor_get(v_a_3028_, 2);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3046_ = v_a_3028_;
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_buildTime_3044_);
lean_inc(v_trace_3043_);
lean_inc(v_log_3040_);
lean_dec(v_a_3028_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
uint8_t v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = 2;
v___x_3049_ = l_Lake_JobAction_merge(v_action_3041_, v___x_3048_);
if (v_isShared_3047_ == 0)
{
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_log_3040_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_trace_3043_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_buildTime_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3063_, sizeof(void*)*3 + 1, v_wantsRebuild_3042_);
v___x_3051_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; 
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*3, v___x_3049_);
v___x_3052_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3022_, v_a_3006_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v___x_3051_);
lean_dec_ref(v_log_3022_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 2);
v___y_3033_ = v_a_3053_;
goto v___jp_3032_;
}
else
{
lean_object* v_a_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3030_);
lean_dec(v_a_3027_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 0);
v_a_3055_ = lean_ctor_get(v___x_3052_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3052_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_inc(v_a_3054_);
lean_dec(v___x_3052_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3054_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_3022_);
v___y_3033_ = v_a_3028_;
goto v___jp_3032_;
}
v___jp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___y_3033_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3027_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___y_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3068_; uint8_t v_oldMode_3069_; 
lean_dec(v_savedTrace_3009_);
v_toBuildConfig_3068_ = lean_ctor_get(v_a_3014_, 0);
v_oldMode_3069_ = lean_ctor_get_uint8(v_toBuildConfig_3068_, sizeof(void*)*3);
if (v_oldMode_3069_ == 0)
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_a_3015_);
return v___x_3072_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_3007_, v_oldTrace_3010_);
if (v___x_3073_ == 0)
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 0;
v___x_3075_ = lean_box(v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_a_3015_);
return v___x_3076_;
}
else
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = 1;
v___x_3078_ = lean_box(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v_a_3015_);
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3080_, lean_object* v_info_3081_, lean_object* v_depTrace_3082_, lean_object* v_savedTrace_3083_, lean_object* v_oldTrace_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3080_, v_info_3081_, v_depTrace_3082_, v_savedTrace_3083_, v_oldTrace_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_oldTrace_3084_);
lean_dec_ref(v_depTrace_3082_);
lean_dec_ref(v_info_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3093_, lean_object* v_build_3094_, uint8_t v_text_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v_a_3108_; lean_object* v_log_3141_; uint8_t v_action_3142_; uint8_t v_wantsRebuild_3143_; lean_object* v_trace_3144_; lean_object* v_buildTime_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3176_; 
v_log_3141_ = lean_ctor_get(v_a_3101_, 0);
v_action_3142_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3);
v_wantsRebuild_3143_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3 + 1);
v_trace_3144_ = lean_ctor_get(v_a_3101_, 1);
v_buildTime_3145_ = lean_ctor_get(v_a_3101_, 2);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_a_3101_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3147_ = v_a_3101_;
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_buildTime_3145_);
lean_inc(v_trace_3144_);
lean_inc(v_log_3141_);
lean_dec(v_a_3101_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
v___jp_3103_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3104_);
lean_ctor_set(v___x_3106_, 1, v_a_3105_);
return v___x_3106_;
}
v___jp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lake_fetchFileTrace___redArg(v_file_3093_, v_text_3095_, v_a_3100_, v_a_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3131_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 1);
v_a_3111_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3131_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3110_);
lean_inc(v_a_3111_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3131_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_log_3115_; uint8_t v_action_3116_; uint8_t v_wantsRebuild_3117_; lean_object* v_buildTime_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3129_; 
v_log_3115_ = lean_ctor_get(v_a_3110_, 0);
v_action_3116_ = lean_ctor_get_uint8(v_a_3110_, sizeof(void*)*3);
v_wantsRebuild_3117_ = lean_ctor_get_uint8(v_a_3110_, sizeof(void*)*3 + 1);
v_buildTime_3118_ = lean_ctor_get(v_a_3110_, 2);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_a_3110_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_a_3110_, 1);
lean_dec(v_unused_3130_);
v___x_3120_ = v_a_3110_;
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_buildTime_3118_);
lean_inc(v_log_3115_);
lean_dec(v_a_3110_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_box(0);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v_a_3111_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_log_3115_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3111_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_buildTime_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3128_, sizeof(void*)*3, v_action_3116_);
lean_ctor_set_uint8(v_reuseFailAlloc_3128_, sizeof(void*)*3 + 1, v_wantsRebuild_3117_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v___x_3124_);
lean_ctor_set(v___x_3113_, 0, v___x_3122_);
v___x_3126_ = v___x_3113_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3132_ = lean_ctor_get(v___x_3109_, 0);
v_a_3133_ = lean_ctor_get(v___x_3109_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3109_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_inc(v_a_3132_);
lean_dec(v___x_3109_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3132_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_traceFile_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3093_);
v_traceFile_3150_ = lean_string_append(v_file_3093_, v___x_3149_);
lean_inc_ref(v_traceFile_3150_);
v___x_3151_ = l_Lake_readTraceFile(v_traceFile_3150_, v_log_3141_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v_mtime_3154_; lean_object* v___x_3156_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3151_, 2);
v_mtime_3154_ = lean_ctor_get(v_trace_3144_, 2);
lean_inc_ref(v_trace_3144_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3153_);
v___x_3156_ = v___x_3147_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3156_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3096_, v_file_3093_, v_trace_3144_, v_a_3152_, v_mtime_3154_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v_a_3159_; uint8_t v___x_3160_; uint8_t v___x_3161_; uint8_t v___x_3162_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
v_a_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3157_, 2);
v___x_3160_ = 0;
v___x_3161_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
v___x_3162_ = l_Lake_instDecidableEqOutputStatus(v___x_3161_, v___x_3160_);
if (v___x_3162_ == 0)
{
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_trace_3144_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
v_a_3108_ = v_a_3159_;
goto v___jp_3107_;
}
else
{
uint8_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = 5;
lean_inc_ref(v_file_3093_);
v___x_3164_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3094_, v_file_3093_, v_a_3096_, v_trace_3144_, v_traceFile_3150_, v___x_3163_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3159_);
lean_dec_ref(v_trace_3144_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 2);
v_a_3108_ = v_a_3165_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3166_; lean_object* v_a_3167_; 
lean_dec_ref(v_file_3093_);
v_a_3166_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3166_);
v_a_3167_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3164_, 2);
v_a_3104_ = v_a_3166_;
v_a_3105_ = v_a_3167_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v_a_3169_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_trace_3144_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3168_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3168_);
v_a_3169_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3157_, 2);
v_a_3104_ = v_a_3168_;
v_a_3105_ = v_a_3169_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v_a_3172_; lean_object* v___x_3174_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3171_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3171_);
v_a_3172_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3151_, 2);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3172_);
v___x_3174_ = v___x_3147_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3172_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3175_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3175_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
v_a_3104_ = v_a_3171_;
v_a_3105_ = v___x_3174_;
goto v___jp_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3177_, lean_object* v_build_3178_, lean_object* v_text_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
uint8_t v_text_boxed_3187_; lean_object* v_res_3188_; 
v_text_boxed_3187_ = lean_unbox(v_text_3179_);
v_res_3188_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3177_, v_build_3178_, v_text_boxed_3187_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec(v_a_3181_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3189_, lean_object* v_info_3190_, lean_object* v_depTrace_3191_, lean_object* v_depHash_3192_, lean_object* v_oldTrace_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3190_, v_depTrace_3191_, v_depHash_3192_, v_oldTrace_3193_, v_a_3197_, v_a_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3201_, lean_object* v_info_3202_, lean_object* v_depTrace_3203_, lean_object* v_depHash_3204_, lean_object* v_oldTrace_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3201_, v_info_3202_, v_depTrace_3203_, v_depHash_3204_, v_oldTrace_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_oldTrace_3205_);
lean_dec(v_depHash_3204_);
lean_dec_ref(v_depTrace_3203_);
lean_dec_ref(v_info_3202_);
lean_dec_ref(v_a_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_file_3215_, uint64_t v___x_3216_, lean_object* v___x_3217_, uint8_t v_useLocalFile_3218_, lean_object* v_____r_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_IO_setAccessRights(v___x_3213_, v___x_3214_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
lean_dec_ref_known(v___x_3221_, 1);
lean_inc_ref(v_file_3215_);
v___x_3222_ = l_Lake_writeFileHash(v_file_3215_, v___x_3216_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3222_, 1);
v___x_3223_ = lean_io_metadata(v___x_3213_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3236_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_modified_3228_; lean_object* v___y_3230_; 
v_modified_3228_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_modified_3228_);
lean_dec(v_a_3224_);
if (v_useLocalFile_3218_ == 0)
{
v___y_3230_ = v___x_3213_;
goto v___jp_3229_;
}
else
{
lean_dec_ref(v___x_3213_);
lean_inc_ref(v_file_3215_);
v___y_3230_ = v_file_3215_;
goto v___jp_3229_;
}
v___jp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3217_);
lean_ctor_set(v___x_3231_, 1, v___y_3230_);
lean_ctor_set(v___x_3231_, 2, v_file_3215_);
lean_ctor_set(v___x_3231_, 3, v_modified_3228_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3232_);
v___x_3234_ = v___x_3226_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3237_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3223_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3223_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3245_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3222_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3222_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3253_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3221_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3221_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_file_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_useLocalFile_3266_, lean_object* v_____r_3267_, lean_object* v___y_3268_){
_start:
{
uint64_t v___x_2969__boxed_3269_; uint8_t v_useLocalFile_boxed_3270_; lean_object* v_res_3271_; 
v___x_2969__boxed_3269_ = lean_unbox_uint64(v___x_3264_);
lean_dec_ref(v___x_3264_);
v_useLocalFile_boxed_3270_ = lean_unbox(v_useLocalFile_3266_);
v_res_3271_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3261_, v___x_3262_, v_file_3263_, v___x_2969__boxed_3269_, v___x_3265_, v_useLocalFile_boxed_3270_, v_____r_3267_);
lean_dec_ref(v___x_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3279_, lean_object* v_file_3280_, lean_object* v_ext_3281_, uint8_t v_text_3282_, uint8_t v_exe_3283_, uint8_t v_useLocalFile_3284_){
_start:
{
lean_object* v_a_3287_; lean_object* v___y_3294_; uint8_t v___x_3305_; 
v___x_3305_ = 1;
if (v_text_3282_ == 0)
{
lean_object* v___x_3306_; 
v___x_3306_ = l_IO_FS_readBinFile(v_file_3280_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; uint64_t v___x_3308_; uint64_t v___x_3309_; uint64_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___y_3315_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = l_Lake_Hash_nil;
v___x_3309_ = lean_byte_array_hash(v_a_3307_);
v___x_3310_ = lean_uint64_mix_hash(v___x_3308_, v___x_3309_);
lean_inc_ref(v_ext_3281_);
v___x_3311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3311_, 0, v_ext_3281_);
lean_ctor_set_uint64(v___x_3311_, sizeof(void*)*1, v___x_3310_);
v___x_3312_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3313_ = l_System_FilePath_join(v_cache_3279_, v___x_3312_);
v___x_3336_ = lean_string_utf8_byte_size(v_ext_3281_);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_nat_dec_eq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3339_ = l_Lake_lowerHexUInt64(v___x_3310_);
v___x_3340_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = lean_string_append(v___x_3341_, v_ext_3281_);
lean_dec_ref(v_ext_3281_);
v___y_3315_ = v___x_3342_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3343_; 
lean_dec_ref(v_ext_3281_);
v___x_3343_ = l_Lake_lowerHexUInt64(v___x_3310_);
v___y_3315_ = v___x_3343_;
goto v___jp_3314_;
}
v___jp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3316_, 0, v___x_3305_);
lean_ctor_set_uint8(v___x_3316_, 1, v_text_3282_);
lean_ctor_set_uint8(v___x_3316_, 2, v_exe_3283_);
lean_inc_ref_n(v___x_3316_, 2);
v___x_3317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
lean_ctor_set(v___x_3317_, 2, v___x_3316_);
v___x_3318_ = l_IO_setAccessRights(v_file_3280_, v___x_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_dec_ref_known(v___x_3318_, 1);
v___x_3319_ = l_Lake_joinRelative(v___x_3313_, v___y_3315_);
v___x_3320_ = l_System_FilePath_pathExists(v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_inc_ref(v___x_3319_);
v___x_3321_ = l_Lake_createParentDirs(v___x_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref_known(v___x_3321_, 1);
v___x_3322_ = lean_io_hard_link(v_file_3280_, v___x_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec_ref_known(v___x_3322_, 1);
lean_dec(v_a_3307_);
v___x_3323_ = lean_box(0);
v___x_3324_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3323_);
lean_dec_ref_known(v___x_3317_, 3);
v___y_3294_ = v___x_3324_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3325_; 
v_a_3325_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3322_, 1);
if (lean_obj_tag(v_a_3325_) == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec_ref_known(v_a_3325_, 2);
lean_dec(v_a_3307_);
v___x_3326_ = lean_box(0);
v___x_3327_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3326_);
lean_dec_ref_known(v___x_3317_, 3);
v___y_3294_ = v___x_3327_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3328_; 
lean_dec(v_a_3325_);
v___x_3328_ = l_Lake_writeBinFileIfNew(v___x_3319_, v_a_3307_);
lean_dec(v_a_3307_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v_a_3329_);
lean_dec_ref_known(v___x_3317_, 3);
v___y_3294_ = v___x_3330_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3331_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref_known(v___x_3317_, 3);
lean_dec_ref_known(v___x_3311_, 1);
lean_dec_ref(v_file_3280_);
v_a_3331_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3328_, 1);
v_a_3287_ = v_a_3331_;
goto v___jp_3286_;
}
}
}
}
else
{
lean_object* v_a_3332_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref_known(v___x_3317_, 3);
lean_dec_ref_known(v___x_3311_, 1);
lean_dec(v_a_3307_);
lean_dec_ref(v_file_3280_);
v_a_3332_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3321_, 1);
v_a_3287_ = v_a_3332_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec(v_a_3307_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3333_);
lean_dec_ref_known(v___x_3317_, 3);
v___y_3294_ = v___x_3334_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3335_; 
lean_dec_ref_known(v___x_3317_, 3);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___x_3313_);
lean_dec_ref_known(v___x_3311_, 1);
lean_dec(v_a_3307_);
lean_dec_ref(v_file_3280_);
v_a_3335_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3318_, 1);
v_a_3287_ = v_a_3335_;
goto v___jp_3286_;
}
}
}
else
{
lean_object* v_a_3344_; 
lean_dec_ref(v_ext_3281_);
lean_dec_ref(v_file_3280_);
lean_dec_ref(v_cache_3279_);
v_a_3344_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3306_, 1);
v_a_3287_ = v_a_3344_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3345_; 
v___x_3345_ = l_IO_FS_readFile(v_file_3280_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; uint64_t v___x_3348_; uint64_t v___x_3349_; uint64_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___y_3355_; lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = l_String_crlfToLf(v_a_3346_);
lean_dec(v_a_3346_);
v___x_3348_ = l_Lake_Hash_nil;
v___x_3349_ = lean_string_hash(v___x_3347_);
v___x_3350_ = lean_uint64_mix_hash(v___x_3348_, v___x_3349_);
lean_inc_ref(v_ext_3281_);
v___x_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3351_, 0, v_ext_3281_);
lean_ctor_set_uint64(v___x_3351_, sizeof(void*)*1, v___x_3350_);
v___x_3352_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3353_ = l_System_FilePath_join(v_cache_3279_, v___x_3352_);
v___x_3369_ = lean_string_utf8_byte_size(v_ext_3281_);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_nat_dec_eq(v___x_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3372_ = l_Lake_lowerHexUInt64(v___x_3350_);
v___x_3373_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3374_ = lean_string_append(v___x_3372_, v___x_3373_);
v___x_3375_ = lean_string_append(v___x_3374_, v_ext_3281_);
lean_dec_ref(v_ext_3281_);
v___y_3355_ = v___x_3375_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3376_; 
lean_dec_ref(v_ext_3281_);
v___x_3376_ = l_Lake_lowerHexUInt64(v___x_3350_);
v___y_3355_ = v___x_3376_;
goto v___jp_3354_;
}
v___jp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3357_ = l_IO_setAccessRights(v_file_3280_, v___x_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
lean_dec_ref_known(v___x_3357_, 1);
v___x_3358_ = l_Lake_joinRelative(v___x_3353_, v___y_3355_);
v___x_3359_ = l_System_FilePath_pathExists(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_inc_ref(v___x_3358_);
v___x_3360_ = l_Lake_createParentDirs(v___x_3358_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref_known(v___x_3360_, 1);
v___x_3361_ = l_Lake_writeFileIfNew(v___x_3358_, v___x_3347_);
lean_dec_ref(v___x_3347_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3358_, v___x_3356_, v_file_3280_, v___x_3350_, v___x_3351_, v_useLocalFile_3284_, v_a_3362_);
v___y_3294_ = v___x_3363_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3364_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref_known(v___x_3351_, 1);
lean_dec_ref(v_file_3280_);
v_a_3364_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3361_, 1);
v_a_3287_ = v_a_3364_;
goto v___jp_3286_;
}
}
else
{
lean_object* v_a_3365_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref_known(v___x_3351_, 1);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3280_);
v_a_3365_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3360_, 1);
v_a_3287_ = v_a_3365_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v___x_3347_);
v___x_3366_ = lean_box(0);
v___x_3367_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3358_, v___x_3356_, v_file_3280_, v___x_3350_, v___x_3351_, v_useLocalFile_3284_, v___x_3366_);
v___y_3294_ = v___x_3367_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3368_; 
lean_dec_ref(v___y_3355_);
lean_dec_ref(v___x_3353_);
lean_dec_ref_known(v___x_3351_, 1);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3280_);
v_a_3368_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3357_, 1);
v_a_3287_ = v_a_3368_;
goto v___jp_3286_;
}
}
}
else
{
lean_object* v_a_3377_; 
lean_dec_ref(v_ext_3281_);
lean_dec_ref(v_file_3280_);
lean_dec_ref(v_cache_3279_);
v_a_3377_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3345_, 1);
v_a_3287_ = v_a_3377_;
goto v___jp_3286_;
}
}
v___jp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3289_ = lean_io_error_to_string(v_a_3287_);
v___x_3290_ = lean_string_append(v___x_3288_, v___x_3289_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = lean_mk_io_user_error(v___x_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
v___jp_3293_:
{
if (lean_obj_tag(v___y_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3303_; 
v_a_3295_ = lean_ctor_get(v___y_3294_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___y_3294_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3297_ = v___y_3294_;
v_isShared_3298_ = v_isSharedCheck_3303_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___y_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3303_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_a_3299_; lean_object* v___x_3301_; 
v_a_3299_ = lean_ctor_get(v_a_3295_, 0);
lean_inc(v_a_3299_);
lean_dec(v_a_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_a_3299_);
v___x_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
else
{
lean_object* v_a_3304_; 
v_a_3304_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___y_3294_, 1);
v_a_3287_ = v_a_3304_;
goto v___jp_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3378_, lean_object* v_file_3379_, lean_object* v_ext_3380_, lean_object* v_text_3381_, lean_object* v_exe_3382_, lean_object* v_useLocalFile_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_text_boxed_3385_; uint8_t v_exe_boxed_3386_; uint8_t v_useLocalFile_boxed_3387_; lean_object* v_res_3388_; 
v_text_boxed_3385_ = lean_unbox(v_text_3381_);
v_exe_boxed_3386_ = lean_unbox(v_exe_3382_);
v_useLocalFile_boxed_3387_ = lean_unbox(v_useLocalFile_3383_);
v_res_3388_ = l_Lake_Cache_saveArtifact(v_cache_3378_, v_file_3379_, v_ext_3380_, v_text_boxed_3385_, v_exe_boxed_3386_, v_useLocalFile_boxed_3387_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3389_){
_start:
{
lean_object* v_lakeCache_3390_; 
v_lakeCache_3390_ = lean_ctor_get(v_x_3389_, 2);
lean_inc_ref(v_lakeCache_3390_);
return v_lakeCache_3390_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3391_);
lean_dec_ref(v_x_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3393_, lean_object* v_ext_3394_, uint8_t v_text_3395_, uint8_t v_exe_3396_, uint8_t v_useLocalFile_3397_, lean_object* v_inst_3398_, lean_object* v_____do__lift_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3400_ = lean_box(v_text_3395_);
v___x_3401_ = lean_box(v_exe_3396_);
v___x_3402_ = lean_box(v_useLocalFile_3397_);
v___x_3403_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3403_, 0, v_____do__lift_3399_);
lean_closure_set(v___x_3403_, 1, v_file_3393_);
lean_closure_set(v___x_3403_, 2, v_ext_3394_);
lean_closure_set(v___x_3403_, 3, v___x_3400_);
lean_closure_set(v___x_3403_, 4, v___x_3401_);
lean_closure_set(v___x_3403_, 5, v___x_3402_);
v___x_3404_ = lean_apply_2(v_inst_3398_, lean_box(0), v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3405_, lean_object* v_ext_3406_, lean_object* v_text_3407_, lean_object* v_exe_3408_, lean_object* v_useLocalFile_3409_, lean_object* v_inst_3410_, lean_object* v_____do__lift_3411_){
_start:
{
uint8_t v_text_boxed_3412_; uint8_t v_exe_boxed_3413_; uint8_t v_useLocalFile_boxed_3414_; lean_object* v_res_3415_; 
v_text_boxed_3412_ = lean_unbox(v_text_3407_);
v_exe_boxed_3413_ = lean_unbox(v_exe_3408_);
v_useLocalFile_boxed_3414_ = lean_unbox(v_useLocalFile_3409_);
v_res_3415_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3405_, v_ext_3406_, v_text_boxed_3412_, v_exe_boxed_3413_, v_useLocalFile_boxed_3414_, v_inst_3410_, v_____do__lift_3411_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_file_3420_, lean_object* v_ext_3421_, uint8_t v_text_3422_, uint8_t v_exe_3423_, uint8_t v_useLocalFile_3424_){
_start:
{
lean_object* v_toApplicative_3425_; lean_object* v_toFunctor_3426_; lean_object* v_toBind_3427_; lean_object* v_map_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_toApplicative_3425_ = lean_ctor_get(v_inst_3419_, 0);
v_toFunctor_3426_ = lean_ctor_get(v_toApplicative_3425_, 0);
lean_inc_ref(v_toFunctor_3426_);
v_toBind_3427_ = lean_ctor_get(v_inst_3419_, 1);
lean_inc(v_toBind_3427_);
lean_dec_ref(v_inst_3419_);
v_map_3428_ = lean_ctor_get(v_toFunctor_3426_, 0);
lean_inc(v_map_3428_);
lean_dec_ref(v_toFunctor_3426_);
v___f_3429_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3430_ = lean_box(v_text_3422_);
v___x_3431_ = lean_box(v_exe_3423_);
v___x_3432_ = lean_box(v_useLocalFile_3424_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3433_, 0, v_file_3420_);
lean_closure_set(v___f_3433_, 1, v_ext_3421_);
lean_closure_set(v___f_3433_, 2, v___x_3430_);
lean_closure_set(v___f_3433_, 3, v___x_3431_);
lean_closure_set(v___f_3433_, 4, v___x_3432_);
lean_closure_set(v___f_3433_, 5, v_inst_3418_);
v___x_3434_ = lean_apply_4(v_map_3428_, lean_box(0), lean_box(0), v___f_3429_, v_inst_3417_);
v___x_3435_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3434_, v___f_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_file_3439_, lean_object* v_ext_3440_, lean_object* v_text_3441_, lean_object* v_exe_3442_, lean_object* v_useLocalFile_3443_){
_start:
{
uint8_t v_text_boxed_3444_; uint8_t v_exe_boxed_3445_; uint8_t v_useLocalFile_boxed_3446_; lean_object* v_res_3447_; 
v_text_boxed_3444_ = lean_unbox(v_text_3441_);
v_exe_boxed_3445_ = lean_unbox(v_exe_3442_);
v_useLocalFile_boxed_3446_ = lean_unbox(v_useLocalFile_3443_);
v_res_3447_ = l_Lake_cacheArtifact___redArg(v_inst_3436_, v_inst_3437_, v_inst_3438_, v_file_3439_, v_ext_3440_, v_text_boxed_3444_, v_exe_boxed_3445_, v_useLocalFile_boxed_3446_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_file_3452_, lean_object* v_ext_3453_, uint8_t v_text_3454_, uint8_t v_exe_3455_, uint8_t v_useLocalFile_3456_){
_start:
{
lean_object* v_toApplicative_3457_; lean_object* v_toFunctor_3458_; lean_object* v_toBind_3459_; lean_object* v_map_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_toApplicative_3457_ = lean_ctor_get(v_inst_3451_, 0);
v_toFunctor_3458_ = lean_ctor_get(v_toApplicative_3457_, 0);
lean_inc_ref(v_toFunctor_3458_);
v_toBind_3459_ = lean_ctor_get(v_inst_3451_, 1);
lean_inc(v_toBind_3459_);
lean_dec_ref(v_inst_3451_);
v_map_3460_ = lean_ctor_get(v_toFunctor_3458_, 0);
lean_inc(v_map_3460_);
lean_dec_ref(v_toFunctor_3458_);
v___f_3461_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3462_ = lean_box(v_text_3454_);
v___x_3463_ = lean_box(v_exe_3455_);
v___x_3464_ = lean_box(v_useLocalFile_3456_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3465_, 0, v_file_3452_);
lean_closure_set(v___f_3465_, 1, v_ext_3453_);
lean_closure_set(v___f_3465_, 2, v___x_3462_);
lean_closure_set(v___f_3465_, 3, v___x_3463_);
lean_closure_set(v___f_3465_, 4, v___x_3464_);
lean_closure_set(v___f_3465_, 5, v_inst_3450_);
v___x_3466_ = lean_apply_4(v_map_3460_, lean_box(0), lean_box(0), v___f_3461_, v_inst_3449_);
v___x_3467_ = lean_apply_4(v_toBind_3459_, lean_box(0), lean_box(0), v___x_3466_, v___f_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3468_, lean_object* v_inst_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_file_3472_, lean_object* v_ext_3473_, lean_object* v_text_3474_, lean_object* v_exe_3475_, lean_object* v_useLocalFile_3476_){
_start:
{
uint8_t v_text_boxed_3477_; uint8_t v_exe_boxed_3478_; uint8_t v_useLocalFile_boxed_3479_; lean_object* v_res_3480_; 
v_text_boxed_3477_ = lean_unbox(v_text_3474_);
v_exe_boxed_3478_ = lean_unbox(v_exe_3475_);
v_useLocalFile_boxed_3479_ = lean_unbox(v_useLocalFile_3476_);
v_res_3480_ = l_Lake_cacheArtifact(v_m_3468_, v_inst_3469_, v_inst_3470_, v_inst_3471_, v_file_3472_, v_ext_3473_, v_text_boxed_3477_, v_exe_boxed_3478_, v_useLocalFile_boxed_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3482_, lean_object* v_x2_3483_){
_start:
{
lean_object* v_message_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_message_3484_ = lean_ctor_get(v_x2_3483_, 0);
v___x_3485_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3486_ = lean_string_append(v_x1_3482_, v___x_3485_);
v___x_3487_ = lean_string_append(v___x_3486_, v_message_3484_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3488_, lean_object* v_x2_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3488_, v_x2_3489_);
lean_dec_ref(v_x2_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3494_, uint64_t v_inputHash_3495_, lean_object* v_pkg_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_toContext_3504_; lean_object* v_log_3505_; uint8_t v_action_3506_; uint8_t v_wantsRebuild_3507_; lean_object* v_trace_3508_; lean_object* v_buildTime_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3604_; 
v_toContext_3504_ = lean_ctor_get(v_a_3501_, 1);
v_log_3505_ = lean_ctor_get(v_a_3502_, 0);
v_action_3506_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3);
v_wantsRebuild_3507_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3 + 1);
v_trace_3508_ = lean_ctor_get(v_a_3502_, 1);
v_buildTime_3509_ = lean_ctor_get(v_a_3502_, 2);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3511_ = v_a_3502_;
v_isShared_3512_ = v_isSharedCheck_3604_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_buildTime_3509_);
lean_inc(v_trace_3508_);
lean_inc(v_log_3505_);
lean_dec(v_a_3502_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3604_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_lakeCache_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_lakeCache_3513_ = lean_ctor_get(v_toContext_3504_, 2);
v___x_3514_ = l_Lake_Package_cacheScope(v_pkg_3496_);
lean_inc_ref(v_lakeCache_3513_);
v___x_3515_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3513_, v___x_3514_, v_inputHash_3495_, v_log_3505_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3591_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_a_3517_ = lean_ctor_get(v___x_3515_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3519_ = v___x_3515_;
v_isShared_3520_ = v_isSharedCheck_3591_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3591_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3517_);
v___x_3522_ = v___x_3511_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3517_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_trace_3508_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_buildTime_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*3, v_action_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*3 + 1, v_wantsRebuild_3507_);
v___x_3522_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
if (lean_obj_tag(v_a_3516_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3585_; 
v_val_3523_ = lean_ctor_get(v_a_3516_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3525_ = v_a_3516_;
v_isShared_3526_ = v_isSharedCheck_3585_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v_a_3516_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3585_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v_r_3529_; lean_object* v___y_3530_; 
lean_inc_ref(v_a_3501_);
lean_inc(v_a_3500_);
lean_inc(v_a_3499_);
lean_inc(v_a_3498_);
v___x_3527_ = lean_apply_8(v_inst_3494_, v_val_3523_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v___x_3522_, lean_box(0));
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3534_; lean_object* v_a_3535_; lean_object* v___x_3537_; 
v_a_3534_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3534_);
v_a_3535_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3527_, 2);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_a_3534_);
v___x_3537_ = v___x_3525_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3534_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
v_r_3529_ = v___x_3537_;
v___y_3530_ = v_a_3535_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v_a_3540_; lean_object* v_log_3541_; uint8_t v_action_3542_; uint8_t v_wantsRebuild_3543_; lean_object* v_trace_3544_; lean_object* v_buildTime_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3525_);
v_a_3539_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_a_3539_);
v_a_3540_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3527_, 2);
v_log_3541_ = lean_ctor_get(v_a_3539_, 0);
v_action_3542_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*3);
v_wantsRebuild_3543_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*3 + 1);
v_trace_3544_ = lean_ctor_get(v_a_3539_, 1);
v_buildTime_3545_ = lean_ctor_get(v_a_3539_, 2);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_a_3539_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3547_ = v_a_3539_;
v_isShared_3548_ = v_isSharedCheck_3584_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_buildTime_3545_);
lean_inc(v_trace_3544_);
lean_inc(v_log_3541_);
lean_dec(v_a_3539_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3584_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___y_3553_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3549_ = lean_array_get_size(v_log_3541_);
lean_inc(v_a_3540_);
v___x_3550_ = l_Array_extract___redArg(v_log_3541_, v_a_3540_, v___x_3549_);
v___x_3551_ = l_Array_shrink___redArg(v_log_3541_, v_a_3540_);
lean_dec(v_a_3540_);
v___x_3561_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3562_ = l_Lake_lowerHexUInt64(v_inputHash_3495_);
v___x_3563_ = lean_unsigned_to_nat(7u);
v___x_3564_ = lean_unsigned_to_nat(0u);
v___x_3565_ = lean_string_utf8_byte_size(v___x_3562_);
lean_inc_ref(v___x_3562_);
v___x_3566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3562_);
lean_ctor_set(v___x_3566_, 1, v___x_3564_);
lean_ctor_set(v___x_3566_, 2, v___x_3565_);
v___x_3567_ = l_String_Slice_Pos_nextn(v___x_3566_, v___x_3564_, v___x_3563_);
lean_dec_ref_known(v___x_3566_, 3);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3562_);
lean_ctor_set(v___x_3568_, 1, v___x_3564_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
v___x_3569_ = l_String_Slice_toString(v___x_3568_);
lean_dec_ref_known(v___x_3568_, 3);
v___x_3570_ = lean_string_append(v___x_3561_, v___x_3569_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3572_ = lean_string_append(v___x_3570_, v___x_3571_);
v___x_3573_ = lean_array_get_size(v___x_3550_);
v___x_3574_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3575_ = lean_nat_dec_lt(v___x_3564_, v___x_3573_);
if (v___x_3575_ == 0)
{
lean_dec_ref(v___x_3550_);
v___y_3553_ = v___x_3572_;
goto v___jp_3552_;
}
else
{
lean_object* v___f_3576_; uint8_t v___x_3577_; 
v___f_3576_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3577_ = lean_nat_dec_le(v___x_3573_, v___x_3573_);
if (v___x_3577_ == 0)
{
if (v___x_3575_ == 0)
{
lean_dec_ref(v___x_3550_);
v___y_3553_ = v___x_3572_;
goto v___jp_3552_;
}
else
{
size_t v___x_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = lean_usize_of_nat(v___x_3573_);
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3574_, v___f_3576_, v___x_3550_, v___x_3578_, v___x_3579_, v___x_3572_);
v___y_3553_ = v___x_3580_;
goto v___jp_3552_;
}
}
else
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3573_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3574_, v___f_3576_, v___x_3550_, v___x_3581_, v___x_3582_, v___x_3572_);
v___y_3553_ = v___x_3583_;
goto v___jp_3552_;
}
}
v___jp_3552_:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3554_ = 2;
v___x_3555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3555_, 0, v___y_3553_);
lean_ctor_set_uint8(v___x_3555_, sizeof(void*)*1, v___x_3554_);
v___x_3556_ = lean_array_push(v___x_3551_, v___x_3555_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3556_);
v___x_3558_ = v___x_3547_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_trace_3544_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_buildTime_3545_);
lean_ctor_set_uint8(v_reuseFailAlloc_3560_, sizeof(void*)*3, v_action_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3560_, sizeof(void*)*3 + 1, v_wantsRebuild_3543_);
v___x_3558_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_box(0);
v_r_3529_ = v___x_3559_;
v___y_3530_ = v___x_3558_;
goto v___jp_3528_;
}
}
}
}
v___jp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___y_3530_);
lean_ctor_set(v___x_3519_, 0, v_r_3529_);
v___x_3532_ = v___x_3519_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___y_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3497_);
lean_dec_ref(v_inst_3494_);
v___x_3586_ = lean_box(0);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3522_);
lean_ctor_set(v___x_3519_, 0, v___x_3586_);
v___x_3588_ = v___x_3519_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___x_3522_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3603_; 
lean_dec_ref(v_a_3497_);
lean_dec_ref(v_inst_3494_);
v_a_3592_ = lean_ctor_get(v___x_3515_, 0);
v_a_3593_ = lean_ctor_get(v___x_3515_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3595_ = v___x_3515_;
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_inc(v_a_3592_);
lean_dec(v___x_3515_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3593_);
v___x_3598_ = v___x_3511_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3593_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_trace_3508_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_buildTime_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, sizeof(void*)*3, v_action_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, sizeof(void*)*3 + 1, v_wantsRebuild_3507_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v___x_3598_);
v___x_3600_ = v___x_3595_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3592_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3605_, lean_object* v_inputHash_3606_, lean_object* v_pkg_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
uint64_t v_inputHash_boxed_3615_; lean_object* v_res_3616_; 
v_inputHash_boxed_3615_ = lean_unbox_uint64(v_inputHash_3606_);
lean_dec_ref(v_inputHash_3606_);
v_res_3616_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3605_, v_inputHash_boxed_3615_, v_pkg_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec(v_a_3609_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3617_, lean_object* v_inst_3618_, uint64_t v_inputHash_3619_, lean_object* v_pkg_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3618_, v_inputHash_3619_, v_pkg_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3629_, lean_object* v_inst_3630_, lean_object* v_inputHash_3631_, lean_object* v_pkg_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
uint64_t v_inputHash_boxed_3640_; lean_object* v_res_3641_; 
v_inputHash_boxed_3640_ = lean_unbox_uint64(v_inputHash_3631_);
lean_dec_ref(v_inputHash_3631_);
v_res_3641_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3629_, v_inst_3630_, v_inputHash_boxed_3640_, v_pkg_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec(v_a_3634_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3642_, lean_object* v_____r_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_a_3642_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v___y_3649_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3654_, lean_object* v_____r_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3654_, v_____r_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3665_, uint64_t v_inputHash_3666_, lean_object* v_savedTrace_3667_, lean_object* v_pkg_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v___y_3677_; lean_object* v_a_3681_; lean_object* v_a_3682_; lean_object* v___y_3697_; 
if (lean_obj_tag(v_savedTrace_3667_) == 2)
{
lean_object* v_data_3712_; uint64_t v_depHash_3713_; lean_object* v_outputs_x3f_3714_; uint8_t v___x_3715_; 
v_data_3712_ = lean_ctor_get(v_savedTrace_3667_, 0);
lean_inc_ref(v_data_3712_);
lean_dec_ref_known(v_savedTrace_3667_, 1);
v_depHash_3713_ = lean_ctor_get_uint64(v_data_3712_, sizeof(void*)*3);
v_outputs_x3f_3714_ = lean_ctor_get(v_data_3712_, 1);
lean_inc(v_outputs_x3f_3714_);
lean_dec_ref(v_data_3712_);
v___x_3715_ = lean_uint64_dec_eq(v_depHash_3713_, v_inputHash_3666_);
if (v___x_3715_ == 0)
{
lean_dec(v_outputs_x3f_3714_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3714_) == 1)
{
lean_object* v_val_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_val_3716_ = lean_ctor_get(v_outputs_x3f_3714_, 0);
lean_inc_n(v_val_3716_, 2);
lean_dec_ref_known(v_outputs_x3f_3714_, 1);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3718_, 0, v_val_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
lean_ctor_set(v___x_3718_, 2, v___x_3717_);
lean_inc_ref(v_a_3673_);
lean_inc(v_a_3672_);
lean_inc(v_a_3671_);
lean_inc(v_a_3670_);
lean_inc_ref(v_a_3669_);
v___x_3719_ = lean_apply_8(v_inst_3665_, v___x_3718_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, lean_box(0));
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_config_3720_; lean_object* v_a_3721_; lean_object* v_a_3722_; lean_object* v_enableArtifactCache_x3f_3723_; lean_object* v_a_3725_; uint8_t v_a_3729_; lean_object* v_a_3730_; 
v_config_3720_ = lean_ctor_get(v_pkg_3668_, 6);
v_a_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3721_);
v_a_3722_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3719_, 2);
v_enableArtifactCache_x3f_3723_ = lean_ctor_get(v_config_3720_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3723_) == 0)
{
lean_object* v_toContext_3762_; lean_object* v_lakeEnv_3763_; lean_object* v_enableArtifactCache_x3f_3764_; 
v_toContext_3762_ = lean_ctor_get(v_a_3673_, 1);
v_lakeEnv_3763_ = lean_ctor_get(v_toContext_3762_, 0);
v_enableArtifactCache_x3f_3764_ = lean_ctor_get(v_lakeEnv_3763_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3764_) == 0)
{
lean_object* v_packages_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v_config_3768_; lean_object* v_enableArtifactCache_x3f_3769_; 
v_packages_3765_ = lean_ctor_get(v_toContext_3762_, 4);
v___x_3766_ = lean_unsigned_to_nat(0u);
v___x_3767_ = lean_array_fget_borrowed(v_packages_3765_, v___x_3766_);
v_config_3768_ = lean_ctor_get(v___x_3767_, 6);
v_enableArtifactCache_x3f_3769_ = lean_ctor_get(v_config_3768_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3769_) == 0)
{
lean_dec(v_val_3716_);
lean_dec_ref(v_pkg_3668_);
v_a_3725_ = v_a_3722_;
goto v___jp_3724_;
}
else
{
lean_object* v_val_3770_; uint8_t v___x_3771_; 
v_val_3770_ = lean_ctor_get(v_enableArtifactCache_x3f_3769_, 0);
v___x_3771_ = lean_unbox(v_val_3770_);
v_a_3729_ = v___x_3771_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
}
else
{
lean_object* v_val_3772_; uint8_t v___x_3773_; 
v_val_3772_ = lean_ctor_get(v_enableArtifactCache_x3f_3764_, 0);
v___x_3773_ = lean_unbox(v_val_3772_);
v_a_3729_ = v___x_3773_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
}
else
{
lean_object* v_val_3774_; uint8_t v___x_3775_; 
v_val_3774_ = lean_ctor_get(v_enableArtifactCache_x3f_3723_, 0);
v___x_3775_ = lean_unbox(v_val_3774_);
v_a_3729_ = v___x_3775_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
v___jp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3726_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3725_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3727_;
goto v___jp_3696_;
}
v___jp_3728_:
{
if (v_a_3729_ == 0)
{
lean_dec(v_val_3716_);
lean_dec_ref(v_pkg_3668_);
v_a_3725_ = v_a_3730_;
goto v___jp_3724_;
}
else
{
lean_object* v_toContext_3731_; lean_object* v_log_3732_; uint8_t v_action_3733_; uint8_t v_wantsRebuild_3734_; lean_object* v_trace_3735_; lean_object* v_buildTime_3736_; lean_object* v_lakeCache_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; 
v_toContext_3731_ = lean_ctor_get(v_a_3673_, 1);
v_log_3732_ = lean_ctor_get(v_a_3730_, 0);
v_action_3733_ = lean_ctor_get_uint8(v_a_3730_, sizeof(void*)*3);
v_wantsRebuild_3734_ = lean_ctor_get_uint8(v_a_3730_, sizeof(void*)*3 + 1);
v_trace_3735_ = lean_ctor_get(v_a_3730_, 1);
v_buildTime_3736_ = lean_ctor_get(v_a_3730_, 2);
v_lakeCache_3737_ = lean_ctor_get(v_toContext_3731_, 2);
v___x_3738_ = l_Lake_Package_cacheScope(v_pkg_3668_);
v___x_3739_ = 0;
lean_inc_ref(v_lakeCache_3737_);
v___x_3740_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3737_, v___x_3738_, v_inputHash_3666_, v_val_3716_, v___x_3717_, v___x_3717_, v___x_3739_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec_ref_known(v___x_3740_, 1);
v___x_3741_ = lean_box(0);
v___x_3742_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3741_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3730_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3742_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3758_; 
lean_inc(v_buildTime_3736_);
lean_inc_ref(v_trace_3735_);
lean_inc_ref(v_log_3732_);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3730_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3759_ = lean_ctor_get(v_a_3730_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_a_3730_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_a_3730_, 0);
lean_dec(v_unused_3761_);
v___x_3744_ = v_a_3730_;
v_isShared_3745_ = v_isSharedCheck_3758_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v_a_3730_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3758_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v_a_3746_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3747_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3748_ = lean_io_error_to_string(v_a_3746_);
v___x_3749_ = lean_string_append(v___x_3747_, v___x_3748_);
lean_dec_ref(v___x_3748_);
v___x_3750_ = 2;
v___x_3751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*1, v___x_3750_);
v___x_3752_ = lean_box(0);
v___x_3753_ = lean_array_push(v_log_3732_, v___x_3751_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3753_);
v___x_3755_ = v___x_3744_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_trace_3735_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_buildTime_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*3, v_action_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*3 + 1, v_wantsRebuild_3734_);
v___x_3755_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3752_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v___x_3755_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3756_;
goto v___jp_3696_;
}
}
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v_a_3777_; 
lean_dec(v_val_3716_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
v_a_3776_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3776_);
v_a_3777_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3719_, 2);
v_a_3681_ = v_a_3776_;
v_a_3682_ = v_a_3777_;
goto v___jp_3680_;
}
}
else
{
lean_dec(v_outputs_x3f_3714_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
}
}
else
{
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec(v_savedTrace_3667_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
v___jp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_box(0);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___y_3677_);
return v___x_3679_;
}
v___jp_3680_:
{
lean_object* v_log_3683_; uint8_t v_action_3684_; uint8_t v_wantsRebuild_3685_; lean_object* v_trace_3686_; lean_object* v_buildTime_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3695_; 
v_log_3683_ = lean_ctor_get(v_a_3682_, 0);
v_action_3684_ = lean_ctor_get_uint8(v_a_3682_, sizeof(void*)*3);
v_wantsRebuild_3685_ = lean_ctor_get_uint8(v_a_3682_, sizeof(void*)*3 + 1);
v_trace_3686_ = lean_ctor_get(v_a_3682_, 1);
v_buildTime_3687_ = lean_ctor_get(v_a_3682_, 2);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3682_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3689_ = v_a_3682_;
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_buildTime_3687_);
lean_inc(v_trace_3686_);
lean_inc(v_log_3683_);
lean_dec(v_a_3682_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = l_Array_shrink___redArg(v_log_3683_, v_a_3681_);
lean_dec(v_a_3681_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3691_);
v___x_3693_ = v___x_3689_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_trace_3686_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_buildTime_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3694_, sizeof(void*)*3, v_action_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3694_, sizeof(void*)*3 + 1, v_wantsRebuild_3685_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
v___y_3677_ = v___x_3693_;
goto v___jp_3676_;
}
}
}
v___jp_3696_:
{
if (lean_obj_tag(v___y_3697_) == 0)
{
lean_object* v_a_3698_; 
v_a_3698_ = lean_ctor_get(v___y_3697_, 0);
if (lean_obj_tag(v_a_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
lean_inc_ref(v_a_3698_);
v_a_3699_ = lean_ctor_get(v___y_3697_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___y_3697_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___y_3697_, 0);
lean_dec(v_unused_3708_);
v___x_3701_ = v___y_3697_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___y_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_a_3703_; lean_object* v___x_3705_; 
v_a_3703_ = lean_ctor_get(v_a_3698_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v_a_3698_, 1);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_a_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3703_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_a_3699_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___y_3697_, 1);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___y_3697_, 2);
v___y_3677_ = v_a_3709_;
goto v___jp_3676_;
}
}
else
{
lean_object* v_a_3710_; lean_object* v_a_3711_; 
v_a_3710_ = lean_ctor_get(v___y_3697_, 0);
lean_inc(v_a_3710_);
v_a_3711_ = lean_ctor_get(v___y_3697_, 1);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___y_3697_, 2);
v_a_3681_ = v_a_3710_;
v_a_3682_ = v_a_3711_;
goto v___jp_3680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3778_, lean_object* v_inputHash_3779_, lean_object* v_savedTrace_3780_, lean_object* v_pkg_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
uint64_t v_inputHash_boxed_3789_; lean_object* v_res_3790_; 
v_inputHash_boxed_3789_ = lean_unbox_uint64(v_inputHash_3779_);
lean_dec_ref(v_inputHash_3779_);
v_res_3790_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3778_, v_inputHash_boxed_3789_, v_savedTrace_3780_, v_pkg_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec(v_a_3783_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3791_, lean_object* v_inst_3792_, uint64_t v_inputHash_3793_, lean_object* v_savedTrace_3794_, lean_object* v_pkg_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3792_, v_inputHash_3793_, v_savedTrace_3794_, v_pkg_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3804_, lean_object* v_inst_3805_, lean_object* v_inputHash_3806_, lean_object* v_savedTrace_3807_, lean_object* v_pkg_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
uint64_t v_inputHash_boxed_3816_; lean_object* v_res_3817_; 
v_inputHash_boxed_3816_ = lean_unbox_uint64(v_inputHash_3806_);
lean_dec_ref(v_inputHash_3806_);
v_res_3817_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3804_, v_inst_3805_, v_inputHash_boxed_3816_, v_savedTrace_3807_, v_pkg_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec(v_a_3810_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3818_, uint64_t v_inputHash_3819_, lean_object* v_savedTrace_3820_, lean_object* v_pkg_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v_a_3830_; lean_object* v___y_3831_; lean_object* v___x_3834_; lean_object* v_a_3835_; 
lean_inc_ref(v_a_3822_);
lean_inc_ref(v_pkg_3821_);
lean_inc_ref(v_inst_3818_);
v___x_3834_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3818_, v_inputHash_3819_, v_savedTrace_3820_, v_pkg_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
if (lean_obj_tag(v_a_3835_) == 1)
{
lean_object* v_a_3836_; lean_object* v_val_3837_; 
lean_dec_ref(v_a_3822_);
lean_dec_ref(v_pkg_3821_);
lean_dec_ref(v_inst_3818_);
v_a_3836_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3834_);
v_val_3837_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_val_3837_);
lean_dec_ref_known(v_a_3835_, 1);
v_a_3830_ = v_val_3837_;
v___y_3831_ = v_a_3836_;
goto v___jp_3829_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3839_; 
lean_dec(v_a_3835_);
v_a_3838_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3834_);
v___x_3839_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3818_, v_inputHash_3819_, v_pkg_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3838_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
if (lean_obj_tag(v_a_3840_) == 1)
{
lean_object* v_a_3841_; lean_object* v_val_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3839_, 1);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3839_, 2);
v_val_3842_ = lean_ctor_get(v_a_3840_, 0);
lean_inc(v_val_3842_);
lean_dec_ref_known(v_a_3840_, 1);
v_a_3830_ = v_val_3842_;
v___y_3831_ = v_a_3841_;
goto v___jp_3829_;
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_a_3840_);
v_a_3843_ = lean_ctor_get(v___x_3839_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v___x_3839_, 0);
lean_dec(v_unused_3852_);
v___x_3845_ = v___x_3839_;
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3839_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = lean_box(0);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3847_);
v___x_3849_ = v___x_3845_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_a_3843_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
return v___x_3839_;
}
}
v___jp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_a_3830_);
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v___y_3831_);
return v___x_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3853_, lean_object* v_inputHash_3854_, lean_object* v_savedTrace_3855_, lean_object* v_pkg_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
uint64_t v_inputHash_boxed_3864_; lean_object* v_res_3865_; 
v_inputHash_boxed_3864_ = lean_unbox_uint64(v_inputHash_3854_);
lean_dec_ref(v_inputHash_3854_);
v_res_3865_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3853_, v_inputHash_boxed_3864_, v_savedTrace_3855_, v_pkg_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec(v_a_3858_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3866_, lean_object* v_inst_3867_, uint64_t v_inputHash_3868_, lean_object* v_savedTrace_3869_, lean_object* v_pkg_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_a_3879_; lean_object* v___y_3880_; lean_object* v___x_3883_; lean_object* v_a_3884_; 
lean_inc_ref(v_a_3871_);
lean_inc_ref(v_pkg_3870_);
lean_inc_ref(v_inst_3867_);
v___x_3883_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3867_, v_inputHash_3868_, v_savedTrace_3869_, v_pkg_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
if (lean_obj_tag(v_a_3884_) == 1)
{
lean_object* v_a_3885_; lean_object* v_val_3886_; 
lean_dec_ref(v_a_3871_);
lean_dec_ref(v_pkg_3870_);
lean_dec_ref(v_inst_3867_);
v_a_3885_ = lean_ctor_get(v___x_3883_, 1);
lean_inc(v_a_3885_);
lean_dec_ref(v___x_3883_);
v_val_3886_ = lean_ctor_get(v_a_3884_, 0);
lean_inc(v_val_3886_);
lean_dec_ref_known(v_a_3884_, 1);
v_a_3879_ = v_val_3886_;
v___y_3880_ = v_a_3885_;
goto v___jp_3878_;
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
lean_dec(v_a_3884_);
v_a_3887_ = lean_ctor_get(v___x_3883_, 1);
lean_inc(v_a_3887_);
lean_dec_ref(v___x_3883_);
v___x_3888_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3867_, v_inputHash_3868_, v_pkg_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3887_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
if (lean_obj_tag(v_a_3889_) == 1)
{
lean_object* v_a_3890_; lean_object* v_val_3891_; 
v_a_3890_ = lean_ctor_get(v___x_3888_, 1);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3888_, 2);
v_val_3891_ = lean_ctor_get(v_a_3889_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v_a_3889_, 1);
v_a_3879_ = v_val_3891_;
v___y_3880_ = v_a_3890_;
goto v___jp_3878_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v_a_3889_);
v_a_3892_ = lean_ctor_get(v___x_3888_, 1);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; 
v_unused_3901_ = lean_ctor_get(v___x_3888_, 0);
lean_dec(v_unused_3901_);
v___x_3894_ = v___x_3888_;
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3888_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = lean_box(0);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3896_);
v___x_3898_ = v___x_3894_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_a_3892_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
return v___x_3888_;
}
}
v___jp_3878_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_a_3879_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___y_3880_);
return v___x_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_inst_3903_, lean_object* v_inputHash_3904_, lean_object* v_savedTrace_3905_, lean_object* v_pkg_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
uint64_t v_inputHash_boxed_3914_; lean_object* v_res_3915_; 
v_inputHash_boxed_3914_ = lean_unbox_uint64(v_inputHash_3904_);
lean_dec_ref(v_inputHash_3904_);
v_res_3915_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3902_, v_inst_3903_, v_inputHash_boxed_3914_, v_savedTrace_3905_, v_pkg_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec(v_a_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3916_, lean_object* v___x_3917_, lean_object* v_mtime_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_inc_ref(v___x_3917_);
v___x_3926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3926_, 0, v_descr_3916_);
lean_ctor_set(v___x_3926_, 1, v___x_3917_);
lean_ctor_set(v___x_3926_, 2, v___x_3917_);
lean_ctor_set(v___x_3926_, 3, v_mtime_3918_);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v___y_3924_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3928_, lean_object* v___x_3929_, lean_object* v_mtime_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lake_resolveArtifact___lam__0(v_descr_3928_, v___x_3929_, v_mtime_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3940_, lean_object* v___f_3941_, lean_object* v_____r_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_log_3950_; uint8_t v_action_3951_; uint8_t v_wantsRebuild_3952_; lean_object* v_trace_3953_; lean_object* v_buildTime_3954_; lean_object* v___x_3955_; 
v_log_3950_ = lean_ctor_get(v___y_3948_, 0);
v_action_3951_ = lean_ctor_get_uint8(v___y_3948_, sizeof(void*)*3);
v_wantsRebuild_3952_ = lean_ctor_get_uint8(v___y_3948_, sizeof(void*)*3 + 1);
v_trace_3953_ = lean_ctor_get(v___y_3948_, 1);
v_buildTime_3954_ = lean_ctor_get(v___y_3948_, 2);
v___x_3955_ = lean_io_metadata(v___x_3940_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v_modified_3957_; lean_object* v___x_3958_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v_modified_3957_ = lean_ctor_get(v_a_3956_, 1);
lean_inc_ref(v_modified_3957_);
lean_dec(v_a_3956_);
lean_inc_ref(v___y_3947_);
lean_inc(v___y_3946_);
lean_inc(v___y_3945_);
lean_inc(v___y_3944_);
v___x_3958_ = lean_apply_8(v___f_3941_, v_modified_3957_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, lean_box(0));
return v___x_3958_;
}
else
{
lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3974_; 
lean_inc(v_buildTime_3954_);
lean_inc_ref(v_trace_3953_);
lean_inc_ref(v_log_3950_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___f_3941_);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___y_3948_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; 
v_unused_3975_ = lean_ctor_get(v___y_3948_, 2);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v___y_3948_, 1);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v___y_3948_, 0);
lean_dec(v_unused_3977_);
v___x_3960_ = v___y_3948_;
v_isShared_3961_ = v_isSharedCheck_3974_;
goto v_resetjp_3959_;
}
else
{
lean_dec(v___y_3948_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3974_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_a_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3971_; 
v_a_3962_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3963_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3964_ = lean_io_error_to_string(v_a_3962_);
v___x_3965_ = lean_string_append(v___x_3963_, v___x_3964_);
lean_dec_ref(v___x_3964_);
v___x_3966_ = 3;
v___x_3967_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set_uint8(v___x_3967_, sizeof(void*)*1, v___x_3966_);
v___x_3968_ = lean_array_get_size(v_log_3950_);
v___x_3969_ = lean_array_push(v_log_3950_, v___x_3967_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3969_);
v___x_3971_ = v___x_3960_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_trace_3953_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_buildTime_3954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3973_, sizeof(void*)*3, v_action_3951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3973_, sizeof(void*)*3 + 1, v_wantsRebuild_3952_);
v___x_3971_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3968_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
return v___x_3972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3978_, lean_object* v___f_3979_, lean_object* v_____r_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lake_resolveArtifact___lam__1(v___x_3978_, v___f_3979_, v_____r_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___x_3978_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_4000_, lean_object* v_service_x3f_4001_, lean_object* v_scope_x3f_4002_, uint8_t v_exe_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v___y_4012_; lean_object* v_a_4013_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v_toContext_4019_; lean_object* v_log_4020_; uint8_t v_action_4021_; uint8_t v_wantsRebuild_4022_; lean_object* v_trace_4023_; lean_object* v_buildTime_4024_; lean_object* v_lakeConfig_4025_; lean_object* v_lakeCache_4026_; uint64_t v_hash_4027_; lean_object* v_ext_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___y_4032_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_toContext_4019_ = lean_ctor_get(v_a_4008_, 1);
v_log_4020_ = lean_ctor_get(v_a_4009_, 0);
v_action_4021_ = lean_ctor_get_uint8(v_a_4009_, sizeof(void*)*3);
v_wantsRebuild_4022_ = lean_ctor_get_uint8(v_a_4009_, sizeof(void*)*3 + 1);
v_trace_4023_ = lean_ctor_get(v_a_4009_, 1);
v_buildTime_4024_ = lean_ctor_get(v_a_4009_, 2);
v_lakeConfig_4025_ = lean_ctor_get(v_toContext_4019_, 1);
v_lakeCache_4026_ = lean_ctor_get(v_toContext_4019_, 2);
v_hash_4027_ = lean_ctor_get_uint64(v_descr_4000_, sizeof(void*)*1);
v_ext_4028_ = lean_ctor_get(v_descr_4000_, 0);
v___x_4029_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4026_);
v___x_4030_ = l_System_FilePath_join(v_lakeCache_4026_, v___x_4029_);
v___x_4130_ = lean_string_utf8_byte_size(v_ext_4028_);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_nat_dec_eq(v___x_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4133_ = l_Lake_lowerHexUInt64(v_hash_4027_);
v___x_4134_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4135_ = lean_string_append(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_string_append(v___x_4135_, v_ext_4028_);
v___y_4032_ = v___x_4136_;
goto v___jp_4031_;
}
else
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lake_lowerHexUInt64(v_hash_4027_);
v___y_4032_ = v___x_4137_;
goto v___jp_4031_;
}
v___jp_4011_:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___y_4012_);
lean_ctor_set(v___x_4014_, 1, v_a_4013_);
return v___x_4014_;
}
v___jp_4015_:
{
if (lean_obj_tag(v___y_4017_) == 0)
{
lean_dec(v___y_4016_);
return v___y_4017_;
}
else
{
lean_object* v_a_4018_; 
v_a_4018_ = lean_ctor_get(v___y_4017_, 1);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___y_4017_, 2);
v___y_4012_ = v___y_4016_;
v_a_4013_ = v_a_4018_;
goto v___jp_4011_;
}
}
v___jp_4031_:
{
lean_object* v___x_4033_; lean_object* v___f_4034_; lean_object* v___x_4035_; 
v___x_4033_ = l_Lake_joinRelative(v___x_4030_, v___y_4032_);
lean_inc_ref(v___x_4033_);
lean_inc_ref(v_descr_4000_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4034_, 0, v_descr_4000_);
lean_closure_set(v___f_4034_, 1, v___x_4033_);
v___x_4035_ = lean_io_metadata(v___x_4033_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_modified_4037_; lean_object* v___x_4038_; 
lean_dec_ref(v___f_4034_);
lean_dec(v_scope_x3f_4002_);
lean_dec(v_service_x3f_4001_);
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v_modified_4037_ = lean_ctor_get(v_a_4036_, 1);
lean_inc_ref(v_modified_4037_);
lean_dec(v_a_4036_);
v___x_4038_ = l_Lake_resolveArtifact___lam__0(v_descr_4000_, v___x_4033_, v_modified_4037_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec_ref(v_a_4004_);
return v___x_4038_;
}
else
{
lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4126_; 
lean_inc(v_buildTime_4024_);
lean_inc_ref(v_trace_4023_);
lean_inc_ref(v_log_4020_);
lean_dec_ref(v_descr_4000_);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_a_4009_);
if (v_isSharedCheck_4126_ == 0)
{
lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; 
v_unused_4127_ = lean_ctor_get(v_a_4009_, 2);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_a_4009_, 1);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_a_4009_, 0);
lean_dec(v_unused_4129_);
v___x_4040_ = v_a_4009_;
v_isShared_4041_ = v_isSharedCheck_4126_;
goto v_resetjp_4039_;
}
else
{
lean_dec(v_a_4009_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4126_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4035_, 1);
if (lean_obj_tag(v_a_4042_) == 11)
{
lean_object* v___x_4043_; 
lean_dec_ref_known(v_a_4042_, 2);
v___x_4043_ = lean_array_get_size(v_log_4020_);
if (lean_obj_tag(v_service_x3f_4001_) == 1)
{
lean_object* v_val_4044_; lean_object* v_cacheServices_4045_; uint8_t v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_val_4044_ = lean_ctor_get(v_service_x3f_4001_, 0);
lean_inc_n(v_val_4044_, 2);
lean_dec_ref_known(v_service_x3f_4001_, 1);
v_cacheServices_4045_ = lean_ctor_get(v_lakeConfig_4025_, 3);
v___x_4046_ = 4;
v___x_4047_ = l_Lake_JobAction_merge(v_action_4021_, v___x_4046_);
v___x_4048_ = lean_box(0);
v___x_4049_ = l_Lean_Name_str___override(v___x_4048_, v_val_4044_);
v___x_4050_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4045_, v___x_4049_);
lean_dec(v___x_4049_);
if (lean_obj_tag(v___x_4050_) == 1)
{
lean_dec(v_val_4044_);
if (lean_obj_tag(v_scope_x3f_4002_) == 1)
{
lean_object* v_val_4051_; lean_object* v_val_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_val_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v___x_4050_, 1);
v_val_4052_ = lean_ctor_get(v_scope_x3f_4002_, 0);
lean_inc(v_val_4052_);
lean_dec_ref_known(v_scope_x3f_4002_, 1);
v___x_4053_ = l_Lake_CacheService_artifactUrl(v_hash_4027_, v_val_4051_, v_val_4052_);
v___x_4054_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4055_ = l_Lake_lowerHexUInt64(v_hash_4027_);
v___x_4056_ = lean_string_append(v___x_4054_, v___x_4055_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4058_ = lean_string_append(v___x_4056_, v___x_4057_);
v___x_4059_ = lean_string_append(v___x_4058_, v___x_4033_);
v___x_4060_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4061_ = lean_string_append(v___x_4059_, v___x_4060_);
v___x_4062_ = lean_string_append(v___x_4061_, v___x_4053_);
v___x_4063_ = 0;
v___x_4064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*1, v___x_4063_);
v___x_4065_ = lean_array_push(v_log_4020_, v___x_4064_);
lean_inc_ref(v___x_4033_);
v___x_4066_ = l_Lake_downloadArtifactCore(v_hash_4027_, v___x_4053_, v___x_4033_, v___x_4065_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; uint8_t v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 1);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 2);
v___x_4068_ = 1;
v___x_4069_ = 0;
v___x_4070_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4070_, 0, v___x_4068_);
lean_ctor_set_uint8(v___x_4070_, 1, v___x_4069_);
lean_ctor_set_uint8(v___x_4070_, 2, v_exe_4003_);
lean_inc_ref_n(v___x_4070_, 2);
v___x_4071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
lean_ctor_set(v___x_4071_, 2, v___x_4070_);
v___x_4072_ = l_IO_setAccessRights(v___x_4033_, v___x_4071_);
lean_dec_ref_known(v___x_4071_, 3);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4074_; 
lean_dec_ref_known(v___x_4072_, 1);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v_a_4067_);
v___x_4074_ = v___x_4040_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4067_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4074_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_ctor_set_uint8(v___x_4074_, sizeof(void*)*3, v___x_4047_);
v___x_4075_ = lean_box(0);
v___x_4076_ = l_Lake_resolveArtifact___lam__1(v___x_4033_, v___f_4034_, v___x_4075_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v___x_4074_);
lean_dec_ref(v___x_4033_);
v___y_4016_ = v___x_4043_;
v___y_4017_ = v___x_4076_;
goto v___jp_4015_;
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v_a_4078_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4072_, 1);
v___x_4079_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4080_ = lean_io_error_to_string(v_a_4078_);
v___x_4081_ = lean_string_append(v___x_4079_, v___x_4080_);
lean_dec_ref(v___x_4080_);
v___x_4082_ = 2;
v___x_4083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*1, v___x_4082_);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_array_push(v_a_4067_, v___x_4083_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4085_);
v___x_4087_ = v___x_4040_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4089_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4087_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; 
lean_ctor_set_uint8(v___x_4087_, sizeof(void*)*3, v___x_4047_);
v___x_4088_ = l_Lake_resolveArtifact___lam__1(v___x_4033_, v___f_4034_, v___x_4084_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v___x_4087_);
lean_dec_ref(v___x_4033_);
v___y_4016_ = v___x_4043_;
v___y_4017_ = v___x_4088_;
goto v___jp_4015_;
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; 
lean_dec_ref(v___f_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v_a_4004_);
v_a_4090_ = lean_ctor_get(v___x_4066_, 1);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4066_, 2);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v_a_4090_);
v___x_4092_ = v___x_4040_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4090_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4093_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_ctor_set_uint8(v___x_4092_, sizeof(void*)*3, v___x_4047_);
v___y_4012_ = v___x_4043_;
v_a_4013_ = v___x_4092_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4097_; 
lean_dec_ref_known(v___x_4050_, 1);
lean_dec_ref(v___f_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v_a_4004_);
lean_dec(v_scope_x3f_4002_);
v___x_4094_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4095_ = lean_array_push(v_log_4020_, v___x_4094_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4095_);
v___x_4097_ = v___x_4040_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4098_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4098_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_ctor_set_uint8(v___x_4097_, sizeof(void*)*3, v___x_4047_);
v___y_4012_ = v___x_4043_;
v_a_4013_ = v___x_4097_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec(v___x_4050_);
lean_dec_ref(v___f_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v_a_4004_);
lean_dec(v_scope_x3f_4002_);
v___x_4099_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4100_ = lean_string_append(v___x_4099_, v_val_4044_);
lean_dec(v_val_4044_);
v___x_4101_ = 3;
v___x_4102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*1, v___x_4101_);
v___x_4103_ = lean_array_push(v_log_4020_, v___x_4102_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4103_);
v___x_4105_ = v___x_4040_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4106_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_ctor_set_uint8(v___x_4105_, sizeof(void*)*3, v___x_4047_);
v___y_4012_ = v___x_4043_;
v_a_4013_ = v___x_4105_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_dec_ref(v___f_4034_);
lean_dec_ref(v_a_4004_);
lean_dec(v_scope_x3f_4002_);
lean_dec(v_service_x3f_4001_);
v___x_4107_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4108_ = lean_string_append(v___x_4107_, v___x_4033_);
lean_dec_ref(v___x_4033_);
v___x_4109_ = 3;
v___x_4110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*1, v___x_4109_);
v___x_4111_ = lean_array_push(v_log_4020_, v___x_4110_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4111_);
v___x_4113_ = v___x_4040_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4114_, sizeof(void*)*3, v_action_4021_);
lean_ctor_set_uint8(v_reuseFailAlloc_4114_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
v___y_4012_ = v___x_4043_;
v_a_4013_ = v___x_4113_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; 
lean_dec_ref(v___f_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v_a_4004_);
lean_dec(v_scope_x3f_4002_);
lean_dec(v_service_x3f_4001_);
v___x_4115_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4116_ = lean_io_error_to_string(v_a_4042_);
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = 3;
v___x_4119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4119_, 0, v___x_4117_);
lean_ctor_set_uint8(v___x_4119_, sizeof(void*)*1, v___x_4118_);
v___x_4120_ = lean_array_get_size(v_log_4020_);
v___x_4121_ = lean_array_push(v_log_4020_, v___x_4119_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4121_);
v___x_4123_ = v___x_4040_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_trace_4023_);
lean_ctor_set(v_reuseFailAlloc_4125_, 2, v_buildTime_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*3, v_action_4021_);
lean_ctor_set_uint8(v_reuseFailAlloc_4125_, sizeof(void*)*3 + 1, v_wantsRebuild_4022_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4120_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
return v___x_4124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4138_, lean_object* v_service_x3f_4139_, lean_object* v_scope_x3f_4140_, lean_object* v_exe_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
uint8_t v_exe_boxed_4149_; lean_object* v_res_4150_; 
v_exe_boxed_4149_ = lean_unbox(v_exe_4141_);
v_res_4150_ = l_Lake_resolveArtifact(v_descr_4138_, v_service_x3f_4139_, v_scope_x3f_4140_, v_exe_boxed_4149_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec(v_a_4143_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4153_, uint8_t v_exe_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_data_4162_; lean_object* v_service_x3f_4163_; lean_object* v_scope_x3f_4164_; lean_object* v___x_4165_; 
v_data_4162_ = lean_ctor_get(v_out_4153_, 0);
lean_inc_n(v_data_4162_, 2);
v_service_x3f_4163_ = lean_ctor_get(v_out_4153_, 1);
lean_inc(v_service_x3f_4163_);
v_scope_x3f_4164_ = lean_ctor_get(v_out_4153_, 2);
lean_inc(v_scope_x3f_4164_);
lean_dec_ref(v_out_4153_);
v___x_4165_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4162_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v_log_4167_; uint8_t v_action_4168_; uint8_t v_wantsRebuild_4169_; lean_object* v_trace_4170_; lean_object* v_buildTime_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v_scope_x3f_4164_);
lean_dec(v_service_x3f_4163_);
lean_dec_ref(v_a_4155_);
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v_log_4167_ = lean_ctor_get(v_a_4160_, 0);
v_action_4168_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*3);
v_wantsRebuild_4169_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*3 + 1);
v_trace_4170_ = lean_ctor_get(v_a_4160_, 1);
v_buildTime_4171_ = lean_ctor_get(v_a_4160_, 2);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_a_4160_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4173_ = v_a_4160_;
v_isShared_4174_ = v_isSharedCheck_4193_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_buildTime_4171_);
lean_inc(v_trace_4170_);
lean_inc(v_log_4167_);
lean_dec(v_a_4160_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4193_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4175_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4176_ = l_Lean_Json_render(v_data_4162_);
v___x_4177_ = lean_unsigned_to_nat(80u);
v___x_4178_ = lean_unsigned_to_nat(2u);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = l_Std_Format_pretty(v___x_4176_, v___x_4177_, v___x_4178_, v___x_4179_);
v___x_4181_ = lean_string_append(v___x_4175_, v___x_4180_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4183_ = lean_string_append(v___x_4181_, v___x_4182_);
v___x_4184_ = lean_string_append(v___x_4183_, v_a_4166_);
lean_dec(v_a_4166_);
v___x_4185_ = 3;
v___x_4186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4186_, 0, v___x_4184_);
lean_ctor_set_uint8(v___x_4186_, sizeof(void*)*1, v___x_4185_);
v___x_4187_ = lean_array_get_size(v_log_4167_);
v___x_4188_ = lean_array_push(v_log_4167_, v___x_4186_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4188_);
v___x_4190_ = v___x_4173_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_trace_4170_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_buildTime_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4192_, sizeof(void*)*3, v_action_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4192_, sizeof(void*)*3 + 1, v_wantsRebuild_4169_);
v___x_4190_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4187_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
return v___x_4191_;
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4195_; 
lean_dec(v_data_4162_);
v_a_4194_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4195_ = l_Lake_resolveArtifact(v_a_4194_, v_service_x3f_4163_, v_scope_x3f_4164_, v_exe_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
return v___x_4195_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4196_, lean_object* v_exe_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
uint8_t v_exe_boxed_4205_; lean_object* v_res_4206_; 
v_exe_boxed_4205_ = lean_unbox(v_exe_4197_);
v_res_4206_ = l_Lake_resolveArtifactOutput(v_out_4196_, v_exe_boxed_4205_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec(v_a_4200_);
lean_dec(v_a_4199_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4207_, lean_object* v_out_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lake_resolveArtifactOutput(v_out_4208_, v_exe_4207_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4217_, lean_object* v_out_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v_exe_boxed_4226_; lean_object* v_res_4227_; 
v_exe_boxed_4226_ = lean_unbox(v_exe_4217_);
v_res_4227_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4226_, v_out_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec(v___y_4220_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4228_){
_start:
{
lean_object* v___x_4229_; lean_object* v___f_4230_; 
v___x_4229_ = lean_box(v_exe_4228_);
v___f_4230_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4230_, 0, v___x_4229_);
return v___f_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4231_){
_start:
{
uint8_t v_exe_boxed_4232_; lean_object* v_res_4233_; 
v_exe_boxed_4232_ = lean_unbox(v_exe_4231_);
v_res_4233_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4232_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4234_, lean_object* v_ext_4235_, uint8_t v_text_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4240_; 
lean_inc_ref(v_path_4234_);
v___x_4240_ = l_Lake_fetchFileHash___redArg(v_path_4234_, v_text_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4259_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_a_4242_ = lean_ctor_get(v___x_4240_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4244_ = v___x_4240_;
v_isShared_4245_ = v_isSharedCheck_4259_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4259_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___x_4255_; 
v___x_4255_ = lean_io_metadata(v_path_4234_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v_modified_4257_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v_modified_4257_ = lean_ctor_get(v_a_4256_, 1);
lean_inc_ref(v_modified_4257_);
lean_dec(v_a_4256_);
v___y_4247_ = v_a_4242_;
v___y_4248_ = v_modified_4257_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4258_; 
lean_dec_ref_known(v___x_4255_, 1);
v___x_4258_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4247_ = v_a_4242_;
v___y_4248_ = v___x_4258_;
goto v___jp_4246_;
}
v___jp_4246_:
{
lean_object* v___x_4249_; uint64_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4249_, 0, v_ext_4235_);
v___x_4250_ = lean_unbox_uint64(v_a_4241_);
lean_dec(v_a_4241_);
lean_ctor_set_uint64(v___x_4249_, sizeof(void*)*1, v___x_4250_);
lean_inc_ref(v_path_4234_);
v___x_4251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4249_);
lean_ctor_set(v___x_4251_, 1, v_path_4234_);
lean_ctor_set(v___x_4251_, 2, v_path_4234_);
lean_ctor_set(v___x_4251_, 3, v___y_4248_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 1, v___y_4247_);
lean_ctor_set(v___x_4244_, 0, v___x_4251_);
v___x_4253_ = v___x_4244_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___y_4247_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_ext_4235_);
lean_dec_ref(v_path_4234_);
v_a_4260_ = lean_ctor_get(v___x_4240_, 0);
v_a_4261_ = lean_ctor_get(v___x_4240_, 1);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4240_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_inc(v_a_4260_);
lean_dec(v___x_4240_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4260_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4269_, lean_object* v_ext_4270_, lean_object* v_text_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
uint8_t v_text_boxed_4275_; lean_object* v_res_4276_; 
v_text_boxed_4275_ = lean_unbox(v_text_4271_);
v_res_4276_ = l_Lake_computeArtifact___redArg(v_path_4269_, v_ext_4270_, v_text_boxed_4275_, v_a_4272_, v_a_4273_);
lean_dec_ref(v_a_4272_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4277_, lean_object* v_ext_4278_, uint8_t v_text_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lake_computeArtifact___redArg(v_path_4277_, v_ext_4278_, v_text_4279_, v_a_4284_, v_a_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4288_, lean_object* v_ext_4289_, lean_object* v_text_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
uint8_t v_text_boxed_4298_; lean_object* v_res_4299_; 
v_text_boxed_4298_ = lean_unbox(v_text_4290_);
v_res_4299_ = l_Lake_computeArtifact(v_path_4288_, v_ext_4289_, v_text_boxed_4298_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4303_, lean_object* v_art_4304_, uint8_t v_exe_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___y_4309_; uint8_t v___x_4322_; 
v___x_4322_ = l_System_FilePath_pathExists(v_file_4303_);
if (v___x_4322_ == 0)
{
lean_object* v_descr_4323_; lean_object* v_path_4324_; lean_object* v___y_4326_; lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_descr_4323_ = lean_ctor_get(v_art_4304_, 0);
v_path_4324_ = lean_ctor_get(v_art_4304_, 1);
v___x_4341_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4342_ = lean_string_append(v___x_4341_, v_path_4324_);
v___x_4343_ = 0;
v___x_4344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set_uint8(v___x_4344_, sizeof(void*)*1, v___x_4343_);
v___x_4345_ = lean_array_push(v_a_4306_, v___x_4344_);
lean_inc_ref(v_file_4303_);
v___x_4346_ = l_Lake_createParentDirs(v_file_4303_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v___x_4347_; 
lean_dec_ref_known(v___x_4346_, 1);
v___x_4347_ = lean_io_hard_link(v_path_4324_, v_file_4303_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_dec_ref_known(v___x_4347_, 1);
v___y_4326_ = v___x_4345_;
goto v___jp_4325_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4349_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4350_ = lean_io_error_to_string(v_a_4348_);
v___x_4351_ = lean_string_append(v___x_4349_, v___x_4350_);
lean_dec_ref(v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*1, v___x_4343_);
v___x_4353_ = lean_array_push(v___x_4345_, v___x_4352_);
v___x_4354_ = l_Lake_copyFile(v_path_4324_, v_file_4303_);
if (lean_obj_tag(v___x_4354_) == 0)
{
uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_dec_ref_known(v___x_4354_, 1);
v___x_4355_ = 1;
v___x_4356_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4356_, 0, v___x_4355_);
lean_ctor_set_uint8(v___x_4356_, 1, v___x_4322_);
lean_ctor_set_uint8(v___x_4356_, 2, v_exe_4305_);
lean_inc_ref_n(v___x_4356_, 2);
v___x_4357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
lean_ctor_set(v___x_4357_, 2, v___x_4356_);
v___x_4358_ = l_IO_setAccessRights(v_file_4303_, v___x_4357_);
lean_dec_ref_known(v___x_4357_, 3);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_dec_ref_known(v___x_4358_, 1);
v___y_4326_ = v___x_4353_;
goto v___jp_4325_;
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = lean_io_error_to_string(v_a_4359_);
v___x_4361_ = 3;
v___x_4362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*1, v___x_4361_);
v___x_4363_ = lean_array_get_size(v___x_4353_);
v___x_4364_ = lean_array_push(v___x_4353_, v___x_4362_);
v___x_4365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
return v___x_4365_;
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4366_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4367_ = lean_io_error_to_string(v_a_4366_);
v___x_4368_ = 3;
v___x_4369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4369_, 0, v___x_4367_);
lean_ctor_set_uint8(v___x_4369_, sizeof(void*)*1, v___x_4368_);
v___x_4370_ = lean_array_get_size(v___x_4353_);
v___x_4371_ = lean_array_push(v___x_4353_, v___x_4369_);
v___x_4372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
return v___x_4372_;
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4373_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4346_, 1);
v___x_4374_ = lean_io_error_to_string(v_a_4373_);
v___x_4375_ = 3;
v___x_4376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set_uint8(v___x_4376_, sizeof(void*)*1, v___x_4375_);
v___x_4377_ = lean_array_get_size(v___x_4345_);
v___x_4378_ = lean_array_push(v___x_4345_, v___x_4376_);
v___x_4379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
return v___x_4379_;
}
v___jp_4325_:
{
uint64_t v_hash_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_hash_4327_ = lean_ctor_get_uint64(v_descr_4323_, sizeof(void*)*1);
v___x_4328_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4329_ = lean_string_append(v___x_4328_, v_file_4303_);
v___x_4330_ = 0;
v___x_4331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set_uint8(v___x_4331_, sizeof(void*)*1, v___x_4330_);
v___x_4332_ = lean_array_push(v___y_4326_, v___x_4331_);
lean_inc_ref(v_file_4303_);
v___x_4333_ = l_Lake_writeFileHash(v_file_4303_, v_hash_4327_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_dec_ref_known(v___x_4333_, 1);
v___y_4309_ = v___x_4332_;
goto v___jp_4308_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = lean_io_error_to_string(v_a_4334_);
v___x_4336_ = 3;
v___x_4337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set_uint8(v___x_4337_, sizeof(void*)*1, v___x_4336_);
v___x_4338_ = lean_array_get_size(v___x_4332_);
v___x_4339_ = lean_array_push(v___x_4332_, v___x_4337_);
v___x_4340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
return v___x_4340_;
}
}
}
else
{
v___y_4309_ = v_a_4306_;
goto v___jp_4308_;
}
v___jp_4308_:
{
lean_object* v_descr_4310_; lean_object* v_mtime_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4319_; 
v_descr_4310_ = lean_ctor_get(v_art_4304_, 0);
v_mtime_4311_ = lean_ctor_get(v_art_4304_, 3);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_art_4304_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; lean_object* v_unused_4321_; 
v_unused_4320_ = lean_ctor_get(v_art_4304_, 2);
lean_dec(v_unused_4320_);
v_unused_4321_ = lean_ctor_get(v_art_4304_, 1);
lean_dec(v_unused_4321_);
v___x_4313_ = v_art_4304_;
v_isShared_4314_ = v_isSharedCheck_4319_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_mtime_4311_);
lean_inc(v_descr_4310_);
lean_dec(v_art_4304_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4319_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
lean_inc_ref(v_file_4303_);
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 2, v_file_4303_);
lean_ctor_set(v___x_4313_, 1, v_file_4303_);
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_descr_4310_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_file_4303_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_file_4303_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_mtime_4311_);
v___x_4316_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; 
v___x_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v___y_4309_);
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4380_, lean_object* v_art_4381_, lean_object* v_exe_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
uint8_t v_exe_boxed_4385_; lean_object* v_res_4386_; 
v_exe_boxed_4385_ = lean_unbox(v_exe_4382_);
v_res_4386_ = l_Lake_restoreArtifact(v_file_4380_, v_art_4381_, v_exe_boxed_4385_, v_a_4383_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4387_, lean_object* v_a_x3f_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; lean_object* v_log_4392_; uint8_t v_action_4393_; uint8_t v_wantsRebuild_4394_; lean_object* v_trace_4395_; lean_object* v_buildTime_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4407_; 
v___x_4391_ = lean_io_mono_ms_now();
v_log_4392_ = lean_ctor_get(v___y_4389_, 0);
v_action_4393_ = lean_ctor_get_uint8(v___y_4389_, sizeof(void*)*3);
v_wantsRebuild_4394_ = lean_ctor_get_uint8(v___y_4389_, sizeof(void*)*3 + 1);
v_trace_4395_ = lean_ctor_get(v___y_4389_, 1);
v_buildTime_4396_ = lean_ctor_get(v___y_4389_, 2);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___y_4389_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4398_ = v___y_4389_;
v_isShared_4399_ = v_isSharedCheck_4407_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_buildTime_4396_);
lean_inc(v_trace_4395_);
lean_inc(v_log_4392_);
lean_dec(v___y_4389_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4407_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4400_ = lean_nat_sub(v___x_4391_, v_val_4387_);
lean_dec(v___x_4391_);
v___x_4401_ = lean_box(0);
v___x_4402_ = lean_nat_add(v_buildTime_4396_, v___x_4400_);
lean_dec(v___x_4400_);
lean_dec(v_buildTime_4396_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 2, v___x_4402_);
v___x_4404_ = v___x_4398_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_log_4392_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_trace_4395_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v___x_4402_);
lean_ctor_set_uint8(v_reuseFailAlloc_4406_, sizeof(void*)*3, v_action_4393_);
lean_ctor_set_uint8(v_reuseFailAlloc_4406_, sizeof(void*)*3 + 1, v_wantsRebuild_4394_);
v___x_4404_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4401_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
return v___x_4405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4408_, lean_object* v_a_x3f_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4408_, v_a_x3f_4409_, v___y_4410_);
lean_dec(v_a_x3f_4409_);
lean_dec(v_val_4408_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4413_, lean_object* v_build_4414_, lean_object* v_traceFile_4415_, lean_object* v_ext_4416_, uint8_t v_text_4417_, lean_object* v_a_4418_, lean_object* v_depTrace_4419_, lean_object* v_traceFile_4420_, uint8_t v_action_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_a_4429_; lean_object* v_a_4430_; lean_object* v_log_4433_; uint8_t v_action_4434_; uint8_t v_wantsRebuild_4435_; lean_object* v_trace_4436_; lean_object* v_buildTime_4437_; lean_object* v_toBuildConfig_4443_; lean_object* v_log_4444_; uint8_t v_action_4445_; uint8_t v_wantsRebuild_4446_; lean_object* v_trace_4447_; lean_object* v_buildTime_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4627_; 
v_toBuildConfig_4443_ = lean_ctor_get(v_a_4425_, 0);
v_log_4444_ = lean_ctor_get(v_a_4426_, 0);
v_action_4445_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3);
v_wantsRebuild_4446_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3 + 1);
v_trace_4447_ = lean_ctor_get(v_a_4426_, 1);
v_buildTime_4448_ = lean_ctor_get(v_a_4426_, 2);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4450_ = v_a_4426_;
v_isShared_4451_ = v_isSharedCheck_4627_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_buildTime_4448_);
lean_inc(v_trace_4447_);
lean_inc(v_log_4444_);
lean_dec(v_a_4426_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4627_;
goto v_resetjp_4449_;
}
v___jp_4428_:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_a_4429_);
lean_ctor_set(v___x_4431_, 1, v_a_4430_);
return v___x_4431_;
}
v___jp_4432_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4438_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4439_ = lean_array_get_size(v_log_4433_);
v___x_4440_ = lean_array_push(v_log_4433_, v___x_4438_);
v___x_4441_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
lean_ctor_set(v___x_4441_, 1, v_trace_4436_);
lean_ctor_set(v___x_4441_, 2, v_buildTime_4437_);
lean_ctor_set_uint8(v___x_4441_, sizeof(void*)*3, v_action_4434_);
lean_ctor_set_uint8(v___x_4441_, sizeof(void*)*3 + 1, v_wantsRebuild_4435_);
v___x_4442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4439_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
return v___x_4442_;
}
v_resetjp_4449_:
{
uint8_t v_noBuild_4452_; uint8_t v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_noBuild_4452_ = lean_ctor_get_uint8(v_toBuildConfig_4443_, sizeof(void*)*3 + 2);
v___x_4453_ = l_Lake_JobAction_merge(v_action_4445_, v_action_4421_);
v___x_4454_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4420_);
v___x_4455_ = l_System_FilePath_addExtension(v_traceFile_4420_, v___x_4454_);
if (v_noBuild_4452_ == 0)
{
lean_object* v___x_4456_; lean_object* v_a_4458_; lean_object* v_a_4459_; lean_object* v___x_4463_; 
v___x_4456_ = lean_io_mono_ms_now();
v___x_4463_ = l_Lake_removeFileIfExists(v_file_4413_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4465_; 
lean_dec_ref_known(v___x_4463_, 1);
lean_inc_ref(v_log_4444_);
if (v_isShared_4451_ == 0)
{
v___x_4465_ = v___x_4450_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_log_4444_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_trace_4447_);
lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_buildTime_4448_);
lean_ctor_set_uint8(v_reuseFailAlloc_4602_, sizeof(void*)*3 + 1, v_wantsRebuild_4446_);
v___x_4465_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4466_; 
lean_ctor_set_uint8(v___x_4465_, sizeof(void*)*3, v___x_4453_);
lean_inc_ref(v_a_4425_);
lean_inc(v_a_4424_);
lean_inc(v_a_4423_);
lean_inc(v_a_4422_);
v___x_4466_ = lean_apply_7(v_build_4414_, v_a_4418_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v___x_4465_, lean_box(0));
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v_log_4468_; uint8_t v_action_4469_; uint8_t v_wantsRebuild_4470_; lean_object* v_trace_4471_; lean_object* v_buildTime_4472_; lean_object* v___x_4473_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 1);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 2);
v_log_4468_ = lean_ctor_get(v_a_4467_, 0);
v_action_4469_ = lean_ctor_get_uint8(v_a_4467_, sizeof(void*)*3);
v_wantsRebuild_4470_ = lean_ctor_get_uint8(v_a_4467_, sizeof(void*)*3 + 1);
v_trace_4471_ = lean_ctor_get(v_a_4467_, 1);
v_buildTime_4472_ = lean_ctor_get(v_a_4467_, 2);
lean_inc_ref(v_file_4413_);
v___x_4473_ = l_Lake_clearFileHash(v_file_4413_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v___x_4474_; 
lean_dec_ref_known(v___x_4473_, 1);
v___x_4474_ = l_Lake_removeFileIfExists(v_traceFile_4415_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4566_; 
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v___x_4474_, 0);
lean_dec(v_unused_4567_);
v___x_4476_ = v___x_4474_;
v_isShared_4477_ = v_isSharedCheck_4566_;
goto v_resetjp_4475_;
}
else
{
lean_dec(v___x_4474_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4566_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lake_computeArtifact___redArg(v_file_4413_, v_ext_4416_, v_text_4417_, v_a_4425_, v_a_4467_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v_a_4480_; lean_object* v_descr_4481_; lean_object* v_log_4482_; uint8_t v_action_4483_; uint8_t v_wantsRebuild_4484_; lean_object* v_trace_4485_; lean_object* v_buildTime_4486_; uint64_t v_hash_4487_; lean_object* v_ext_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___y_4493_; lean_object* v___x_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 1);
lean_inc(v_a_4479_);
v_a_4480_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4478_, 2);
v_descr_4481_ = lean_ctor_get(v_a_4480_, 0);
v_log_4482_ = lean_ctor_get(v_a_4479_, 0);
v_action_4483_ = lean_ctor_get_uint8(v_a_4479_, sizeof(void*)*3);
v_wantsRebuild_4484_ = lean_ctor_get_uint8(v_a_4479_, sizeof(void*)*3 + 1);
v_trace_4485_ = lean_ctor_get(v_a_4479_, 1);
v_buildTime_4486_ = lean_ctor_get(v_a_4479_, 2);
v_hash_4487_ = lean_ctor_get_uint64(v_descr_4481_, sizeof(void*)*1);
v_ext_4488_ = lean_ctor_get(v_descr_4481_, 0);
v___x_4489_ = lean_array_get_size(v_log_4444_);
lean_dec_ref(v_log_4444_);
v___x_4490_ = lean_array_get_size(v_log_4482_);
v___x_4491_ = l_Array_extract___redArg(v_log_4482_, v___x_4489_, v___x_4490_);
v___x_4556_ = lean_string_utf8_byte_size(v_ext_4488_);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = lean_nat_dec_eq(v___x_4556_, v___x_4557_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4559_ = l_Lake_lowerHexUInt64(v_hash_4487_);
v___x_4560_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4561_ = lean_string_append(v___x_4559_, v___x_4560_);
v___x_4562_ = lean_string_append(v___x_4561_, v_ext_4488_);
v___y_4493_ = v___x_4562_;
goto v___jp_4492_;
}
else
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lake_lowerHexUInt64(v_hash_4487_);
v___y_4493_ = v___x_4563_;
goto v___jp_4492_;
}
v___jp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 3);
lean_ctor_set(v___x_4476_, 0, v___y_4493_);
v___x_4495_ = v___x_4476_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___y_4493_);
v___x_4495_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4496_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4419_, v___x_4495_, v___x_4491_);
v___x_4497_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4420_, v___x_4496_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4538_; 
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4538_ == 0)
{
lean_object* v_unused_4539_; 
v_unused_4539_ = lean_ctor_get(v___x_4497_, 0);
lean_dec(v_unused_4539_);
v___x_4499_ = v___x_4497_;
v_isShared_4500_ = v_isSharedCheck_4538_;
goto v_resetjp_4498_;
}
else
{
lean_dec(v___x_4497_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4538_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lake_removeFileIfExists(v___x_4455_);
lean_dec_ref(v___x_4455_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4521_; 
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4521_ == 0)
{
lean_object* v_unused_4522_; 
v_unused_4522_ = lean_ctor_get(v___x_4501_, 0);
lean_dec(v_unused_4522_);
v___x_4503_ = v___x_4501_;
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
else
{
lean_dec(v___x_4501_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
lean_inc(v_a_4480_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v_a_4480_);
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4480_);
v___x_4506_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4508_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set_tag(v___x_4499_, 1);
lean_ctor_set(v___x_4499_, 0, v___x_4506_);
v___x_4508_ = v___x_4499_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
v___x_4509_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4456_, v___x_4508_, v_a_4479_);
lean_dec_ref(v___x_4508_);
lean_dec(v___x_4456_);
v_a_4510_ = lean_ctor_get(v___x_4509_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v___x_4509_, 0);
lean_dec(v_unused_4518_);
v___x_4512_ = v___x_4509_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4509_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v_a_4480_);
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4480_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
}
else
{
lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4534_; 
lean_inc(v_buildTime_4486_);
lean_inc_ref(v_trace_4485_);
lean_inc_ref(v_log_4482_);
lean_del_object(v___x_4499_);
lean_dec(v_a_4480_);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_a_4479_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; lean_object* v_unused_4536_; lean_object* v_unused_4537_; 
v_unused_4535_ = lean_ctor_get(v_a_4479_, 2);
lean_dec(v_unused_4535_);
v_unused_4536_ = lean_ctor_get(v_a_4479_, 1);
lean_dec(v_unused_4536_);
v_unused_4537_ = lean_ctor_get(v_a_4479_, 0);
lean_dec(v_unused_4537_);
v___x_4524_ = v_a_4479_;
v_isShared_4525_ = v_isSharedCheck_4534_;
goto v_resetjp_4523_;
}
else
{
lean_dec(v_a_4479_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4534_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v_a_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
v_a_4526_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4527_ = lean_io_error_to_string(v_a_4526_);
v___x_4528_ = 3;
v___x_4529_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4529_, 0, v___x_4527_);
lean_ctor_set_uint8(v___x_4529_, sizeof(void*)*1, v___x_4528_);
v___x_4530_ = lean_array_push(v_log_4482_, v___x_4529_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v___x_4530_);
v___x_4532_ = v___x_4524_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v_trace_4485_);
lean_ctor_set(v_reuseFailAlloc_4533_, 2, v_buildTime_4486_);
lean_ctor_set_uint8(v_reuseFailAlloc_4533_, sizeof(void*)*3, v_action_4483_);
lean_ctor_set_uint8(v_reuseFailAlloc_4533_, sizeof(void*)*3 + 1, v_wantsRebuild_4484_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
v_a_4458_ = v___x_4490_;
v_a_4459_ = v___x_4532_;
goto v___jp_4457_;
}
}
}
}
}
else
{
lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4551_; 
lean_inc(v_buildTime_4486_);
lean_inc_ref(v_trace_4485_);
lean_inc_ref(v_log_4482_);
lean_dec(v_a_4480_);
lean_dec_ref(v___x_4455_);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_a_4479_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; lean_object* v_unused_4553_; lean_object* v_unused_4554_; 
v_unused_4552_ = lean_ctor_get(v_a_4479_, 2);
lean_dec(v_unused_4552_);
v_unused_4553_ = lean_ctor_get(v_a_4479_, 1);
lean_dec(v_unused_4553_);
v_unused_4554_ = lean_ctor_get(v_a_4479_, 0);
lean_dec(v_unused_4554_);
v___x_4541_ = v_a_4479_;
v_isShared_4542_ = v_isSharedCheck_4551_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v_a_4479_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4551_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v_a_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
v_a_4543_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4544_ = lean_io_error_to_string(v_a_4543_);
v___x_4545_ = 3;
v___x_4546_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4546_, 0, v___x_4544_);
lean_ctor_set_uint8(v___x_4546_, sizeof(void*)*1, v___x_4545_);
v___x_4547_ = lean_array_push(v_log_4482_, v___x_4546_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4547_);
v___x_4549_ = v___x_4541_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_trace_4485_);
lean_ctor_set(v_reuseFailAlloc_4550_, 2, v_buildTime_4486_);
lean_ctor_set_uint8(v_reuseFailAlloc_4550_, sizeof(void*)*3, v_action_4483_);
lean_ctor_set_uint8(v_reuseFailAlloc_4550_, sizeof(void*)*3 + 1, v_wantsRebuild_4484_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
v_a_4458_ = v___x_4490_;
v_a_4459_ = v___x_4549_;
goto v___jp_4457_;
}
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v_a_4565_; 
lean_del_object(v___x_4476_);
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_log_4444_);
lean_dec_ref(v_traceFile_4420_);
v_a_4564_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4564_);
v_a_4565_ = lean_ctor_get(v___x_4478_, 1);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4478_, 2);
v_a_4458_ = v_a_4564_;
v_a_4459_ = v_a_4565_;
goto v___jp_4457_;
}
}
}
else
{
lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4580_; 
lean_inc(v_buildTime_4472_);
lean_inc_ref(v_trace_4471_);
lean_inc_ref(v_log_4468_);
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_log_4444_);
lean_dec_ref(v_traceFile_4420_);
lean_dec_ref(v_ext_4416_);
lean_dec_ref(v_file_4413_);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4580_ == 0)
{
lean_object* v_unused_4581_; lean_object* v_unused_4582_; lean_object* v_unused_4583_; 
v_unused_4581_ = lean_ctor_get(v_a_4467_, 2);
lean_dec(v_unused_4581_);
v_unused_4582_ = lean_ctor_get(v_a_4467_, 1);
lean_dec(v_unused_4582_);
v_unused_4583_ = lean_ctor_get(v_a_4467_, 0);
lean_dec(v_unused_4583_);
v___x_4569_ = v_a_4467_;
v_isShared_4570_ = v_isSharedCheck_4580_;
goto v_resetjp_4568_;
}
else
{
lean_dec(v_a_4467_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4580_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v_a_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v_a_4571_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4572_ = lean_io_error_to_string(v_a_4571_);
v___x_4573_ = 3;
v___x_4574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set_uint8(v___x_4574_, sizeof(void*)*1, v___x_4573_);
v___x_4575_ = lean_array_get_size(v_log_4468_);
v___x_4576_ = lean_array_push(v_log_4468_, v___x_4574_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4576_);
v___x_4578_ = v___x_4569_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_trace_4471_);
lean_ctor_set(v_reuseFailAlloc_4579_, 2, v_buildTime_4472_);
lean_ctor_set_uint8(v_reuseFailAlloc_4579_, sizeof(void*)*3, v_action_4469_);
lean_ctor_set_uint8(v_reuseFailAlloc_4579_, sizeof(void*)*3 + 1, v_wantsRebuild_4470_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
v_a_4458_ = v___x_4575_;
v_a_4459_ = v___x_4578_;
goto v___jp_4457_;
}
}
}
}
else
{
lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4596_; 
lean_inc(v_buildTime_4472_);
lean_inc_ref(v_trace_4471_);
lean_inc_ref(v_log_4468_);
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_log_4444_);
lean_dec_ref(v_traceFile_4420_);
lean_dec_ref(v_ext_4416_);
lean_dec_ref(v_file_4413_);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4596_ == 0)
{
lean_object* v_unused_4597_; lean_object* v_unused_4598_; lean_object* v_unused_4599_; 
v_unused_4597_ = lean_ctor_get(v_a_4467_, 2);
lean_dec(v_unused_4597_);
v_unused_4598_ = lean_ctor_get(v_a_4467_, 1);
lean_dec(v_unused_4598_);
v_unused_4599_ = lean_ctor_get(v_a_4467_, 0);
lean_dec(v_unused_4599_);
v___x_4585_ = v_a_4467_;
v_isShared_4586_ = v_isSharedCheck_4596_;
goto v_resetjp_4584_;
}
else
{
lean_dec(v_a_4467_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4596_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v_a_4587_; lean_object* v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v_a_4587_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4588_ = lean_io_error_to_string(v_a_4587_);
v___x_4589_ = 3;
v___x_4590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4590_, 0, v___x_4588_);
lean_ctor_set_uint8(v___x_4590_, sizeof(void*)*1, v___x_4589_);
v___x_4591_ = lean_array_get_size(v_log_4468_);
v___x_4592_ = lean_array_push(v_log_4468_, v___x_4590_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v___x_4592_);
v___x_4594_ = v___x_4585_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_trace_4471_);
lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_buildTime_4472_);
lean_ctor_set_uint8(v_reuseFailAlloc_4595_, sizeof(void*)*3, v_action_4469_);
lean_ctor_set_uint8(v_reuseFailAlloc_4595_, sizeof(void*)*3 + 1, v_wantsRebuild_4470_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
v_a_4458_ = v___x_4591_;
v_a_4459_ = v___x_4594_;
goto v___jp_4457_;
}
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v_a_4601_; 
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_log_4444_);
lean_dec_ref(v_traceFile_4420_);
lean_dec_ref(v_ext_4416_);
lean_dec_ref(v_file_4413_);
v_a_4600_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4600_);
v_a_4601_ = lean_ctor_get(v___x_4466_, 1);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4466_, 2);
v_a_4458_ = v_a_4600_;
v_a_4459_ = v_a_4601_;
goto v___jp_4457_;
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4610_; 
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_traceFile_4420_);
lean_dec_ref(v_a_4418_);
lean_dec_ref(v_ext_4416_);
lean_dec_ref(v_build_4414_);
lean_dec_ref(v_file_4413_);
v_a_4603_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4463_, 1);
v___x_4604_ = lean_io_error_to_string(v_a_4603_);
v___x_4605_ = 3;
v___x_4606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4606_, 0, v___x_4604_);
lean_ctor_set_uint8(v___x_4606_, sizeof(void*)*1, v___x_4605_);
v___x_4607_ = lean_array_get_size(v_log_4444_);
v___x_4608_ = lean_array_push(v_log_4444_, v___x_4606_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4608_);
v___x_4610_ = v___x_4450_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_trace_4447_);
lean_ctor_set(v_reuseFailAlloc_4611_, 2, v_buildTime_4448_);
lean_ctor_set_uint8(v_reuseFailAlloc_4611_, sizeof(void*)*3 + 1, v_wantsRebuild_4446_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_ctor_set_uint8(v___x_4610_, sizeof(void*)*3, v___x_4453_);
v_a_4458_ = v___x_4607_;
v_a_4459_ = v___x_4610_;
goto v___jp_4457_;
}
}
v___jp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v_a_4462_; 
v___x_4460_ = lean_box(0);
v___x_4461_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4456_, v___x_4460_, v_a_4459_);
lean_dec(v___x_4456_);
v_a_4462_ = lean_ctor_get(v___x_4461_, 1);
lean_inc(v_a_4462_);
lean_dec_ref(v___x_4461_);
v_a_4429_ = v_a_4458_;
v_a_4430_ = v_a_4462_;
goto v___jp_4428_;
}
}
else
{
uint8_t v___x_4612_; 
lean_dec_ref(v_a_4418_);
lean_dec_ref(v_ext_4416_);
lean_dec_ref(v_build_4414_);
lean_dec_ref(v_file_4413_);
v___x_4612_ = l_System_FilePath_pathExists(v_traceFile_4420_);
lean_dec_ref(v_traceFile_4420_);
if (v___x_4612_ == 0)
{
lean_dec_ref(v___x_4455_);
lean_del_object(v___x_4450_);
v_log_4433_ = v_log_4444_;
v_action_4434_ = v___x_4453_;
v_wantsRebuild_4435_ = v_noBuild_4452_;
v_trace_4436_ = v_trace_4447_;
v_buildTime_4437_ = v_buildTime_4448_;
goto v___jp_4432_;
}
else
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4613_ = lean_box(0);
v___x_4614_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4615_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4419_, v___x_4613_, v___x_4614_);
v___x_4616_ = l_Lake_BuildMetadata_writeFile(v___x_4455_, v___x_4615_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_dec_ref_known(v___x_4616_, 1);
lean_del_object(v___x_4450_);
v_log_4433_ = v_log_4444_;
v_action_4434_ = v___x_4453_;
v_wantsRebuild_4435_ = v_noBuild_4452_;
v_trace_4436_ = v_trace_4447_;
v_buildTime_4437_ = v_buildTime_4448_;
goto v___jp_4432_;
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v___x_4616_, 1);
v___x_4618_ = lean_io_error_to_string(v_a_4617_);
v___x_4619_ = 3;
v___x_4620_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4620_, 0, v___x_4618_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*1, v___x_4619_);
v___x_4621_ = lean_array_get_size(v_log_4444_);
v___x_4622_ = lean_array_push(v_log_4444_, v___x_4620_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4622_);
v___x_4624_ = v___x_4450_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4622_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_trace_4447_);
lean_ctor_set(v_reuseFailAlloc_4626_, 2, v_buildTime_4448_);
v___x_4624_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
lean_object* v___x_4625_; 
lean_ctor_set_uint8(v___x_4624_, sizeof(void*)*3, v___x_4453_);
lean_ctor_set_uint8(v___x_4624_, sizeof(void*)*3 + 1, v_noBuild_4452_);
v___x_4625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4621_);
lean_ctor_set(v___x_4625_, 1, v___x_4624_);
return v___x_4625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4628_, lean_object* v_build_4629_, lean_object* v_traceFile_4630_, lean_object* v_ext_4631_, lean_object* v_text_4632_, lean_object* v_a_4633_, lean_object* v_depTrace_4634_, lean_object* v_traceFile_4635_, lean_object* v_action_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
uint8_t v_text_boxed_4643_; uint8_t v_action_boxed_4644_; lean_object* v_res_4645_; 
v_text_boxed_4643_ = lean_unbox(v_text_4632_);
v_action_boxed_4644_ = lean_unbox(v_action_4636_);
v_res_4645_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4628_, v_build_4629_, v_traceFile_4630_, v_ext_4631_, v_text_boxed_4643_, v_a_4633_, v_depTrace_4634_, v_traceFile_4635_, v_action_boxed_4644_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec_ref(v_depTrace_4634_);
lean_dec_ref(v_traceFile_4630_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4646_, lean_object* v_build_4647_, uint8_t v_text_4648_, lean_object* v_ext_4649_, lean_object* v_depTrace_4650_, lean_object* v_traceFile_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
uint8_t v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = 5;
lean_inc_ref(v_traceFile_4651_);
v___x_4660_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4646_, v_build_4647_, v_traceFile_4651_, v_ext_4649_, v_text_4648_, v_a_4652_, v_depTrace_4650_, v_traceFile_4651_, v___x_4659_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec_ref(v_traceFile_4651_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4661_, lean_object* v_build_4662_, lean_object* v_text_4663_, lean_object* v_ext_4664_, lean_object* v_depTrace_4665_, lean_object* v_traceFile_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
uint8_t v_text_boxed_4674_; lean_object* v_res_4675_; 
v_text_boxed_4674_ = lean_unbox(v_text_4663_);
v_res_4675_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4661_, v_build_4662_, v_text_boxed_4674_, v_ext_4664_, v_depTrace_4665_, v_traceFile_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_depTrace_4665_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4677_, lean_object* v_traceFile_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v_log_4681_; uint8_t v_action_4682_; uint8_t v_wantsRebuild_4683_; lean_object* v_trace_4684_; lean_object* v_buildTime_4685_; lean_object* v___x_4686_; 
v_log_4681_ = lean_ctor_get(v_a_4679_, 0);
v_action_4682_ = lean_ctor_get_uint8(v_a_4679_, sizeof(void*)*3);
v_wantsRebuild_4683_ = lean_ctor_get_uint8(v_a_4679_, sizeof(void*)*3 + 1);
v_trace_4684_ = lean_ctor_get(v_a_4679_, 1);
v_buildTime_4685_ = lean_ctor_get(v_a_4679_, 2);
v___x_4686_ = lean_io_metadata(v_traceFile_4678_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v_modified_4688_; lean_object* v_descr_4689_; lean_object* v_path_4690_; lean_object* v_name_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4699_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v_modified_4688_ = lean_ctor_get(v_a_4687_, 1);
lean_inc_ref(v_modified_4688_);
lean_dec(v_a_4687_);
v_descr_4689_ = lean_ctor_get(v_art_4677_, 0);
v_path_4690_ = lean_ctor_get(v_art_4677_, 1);
v_name_4691_ = lean_ctor_get(v_art_4677_, 2);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_art_4677_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; 
v_unused_4700_ = lean_ctor_get(v_art_4677_, 3);
lean_dec(v_unused_4700_);
v___x_4693_ = v_art_4677_;
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_name_4691_);
lean_inc(v_path_4690_);
lean_inc(v_descr_4689_);
lean_dec(v_art_4677_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 3, v_modified_4688_);
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_descr_4689_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_path_4690_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_name_4691_);
lean_ctor_set(v_reuseFailAlloc_4698_, 3, v_modified_4688_);
v___x_4696_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v_a_4679_);
return v___x_4697_;
}
}
}
else
{
lean_object* v_a_4701_; 
v_a_4701_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4686_, 1);
if (lean_obj_tag(v_a_4701_) == 11)
{
lean_object* v___x_4702_; 
lean_dec_ref_known(v_a_4701_, 2);
v___x_4702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4702_, 0, v_art_4677_);
lean_ctor_set(v___x_4702_, 1, v_a_4679_);
return v___x_4702_;
}
else
{
lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4717_; 
lean_inc(v_buildTime_4685_);
lean_inc_ref(v_trace_4684_);
lean_inc_ref(v_log_4681_);
lean_dec_ref(v_art_4677_);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_a_4679_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; lean_object* v_unused_4719_; lean_object* v_unused_4720_; 
v_unused_4718_ = lean_ctor_get(v_a_4679_, 2);
lean_dec(v_unused_4718_);
v_unused_4719_ = lean_ctor_get(v_a_4679_, 1);
lean_dec(v_unused_4719_);
v_unused_4720_ = lean_ctor_get(v_a_4679_, 0);
lean_dec(v_unused_4720_);
v___x_4704_ = v_a_4679_;
v_isShared_4705_ = v_isSharedCheck_4717_;
goto v_resetjp_4703_;
}
else
{
lean_dec(v_a_4679_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4717_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4706_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4707_ = lean_io_error_to_string(v_a_4701_);
v___x_4708_ = lean_string_append(v___x_4706_, v___x_4707_);
lean_dec_ref(v___x_4707_);
v___x_4709_ = 3;
v___x_4710_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4710_, 0, v___x_4708_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*1, v___x_4709_);
v___x_4711_ = lean_array_get_size(v_log_4681_);
v___x_4712_ = lean_array_push(v_log_4681_, v___x_4710_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4712_);
v___x_4714_ = v___x_4704_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_trace_4684_);
lean_ctor_set(v_reuseFailAlloc_4716_, 2, v_buildTime_4685_);
lean_ctor_set_uint8(v_reuseFailAlloc_4716_, sizeof(void*)*3, v_action_4682_);
lean_ctor_set_uint8(v_reuseFailAlloc_4716_, sizeof(void*)*3 + 1, v_wantsRebuild_4683_);
v___x_4714_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4715_; 
v___x_4715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4711_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
return v___x_4715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4721_, lean_object* v_traceFile_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4721_, v_traceFile_4722_, v_a_4723_);
lean_dec_ref(v_traceFile_4722_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4726_, lean_object* v_traceFile_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4726_, v_traceFile_4727_, v_a_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4736_, lean_object* v_traceFile_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4736_, v_traceFile_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec(v_a_4740_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec_ref(v_traceFile_4737_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4746_, lean_object* v_____r_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4755_, 0, v_a_4746_);
v___x_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
v___x_4757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
lean_ctor_set(v___x_4757_, 1, v___y_4753_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4758_, lean_object* v_____r_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4758_, v_____r_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4768_, lean_object* v___y_4769_, uint64_t v_inputHash_4770_, lean_object* v_savedTrace_4771_, lean_object* v_pkg_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___y_4780_; lean_object* v_a_4784_; lean_object* v_a_4785_; lean_object* v___y_4800_; 
if (lean_obj_tag(v_savedTrace_4771_) == 2)
{
lean_object* v_data_4815_; uint64_t v_depHash_4816_; lean_object* v_outputs_x3f_4817_; uint8_t v___x_4818_; 
v_data_4815_ = lean_ctor_get(v_savedTrace_4771_, 0);
lean_inc_ref(v_data_4815_);
lean_dec_ref_known(v_savedTrace_4771_, 1);
v_depHash_4816_ = lean_ctor_get_uint64(v_data_4815_, sizeof(void*)*3);
v_outputs_x3f_4817_ = lean_ctor_get(v_data_4815_, 1);
lean_inc(v_outputs_x3f_4817_);
lean_dec_ref(v_data_4815_);
v___x_4818_ = lean_uint64_dec_eq(v_depHash_4816_, v_inputHash_4770_);
if (v___x_4818_ == 0)
{
lean_dec(v_outputs_x3f_4817_);
lean_dec_ref(v_pkg_4772_);
lean_dec_ref(v___y_4769_);
v___y_4780_ = v_a_4777_;
goto v___jp_4779_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4817_) == 1)
{
lean_object* v_val_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v_val_4819_ = lean_ctor_get(v_outputs_x3f_4817_, 0);
lean_inc_n(v_val_4819_, 2);
lean_dec_ref_known(v_outputs_x3f_4817_, 1);
v___x_4820_ = lean_box(0);
v___x_4821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4821_, 0, v_val_4819_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
lean_ctor_set(v___x_4821_, 2, v___x_4820_);
lean_inc_ref(v___y_4769_);
v___x_4822_ = l_Lake_resolveArtifactOutput(v___x_4821_, v_exe_4768_, v___y_4769_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_config_4823_; lean_object* v_a_4824_; lean_object* v_a_4825_; lean_object* v_enableArtifactCache_x3f_4826_; lean_object* v_a_4828_; uint8_t v_a_4832_; lean_object* v_a_4833_; 
v_config_4823_ = lean_ctor_get(v_pkg_4772_, 6);
v_a_4824_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4824_);
v_a_4825_ = lean_ctor_get(v___x_4822_, 1);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4822_, 2);
v_enableArtifactCache_x3f_4826_ = lean_ctor_get(v_config_4823_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4826_) == 0)
{
lean_object* v_toContext_4865_; lean_object* v_lakeEnv_4866_; lean_object* v_enableArtifactCache_x3f_4867_; 
v_toContext_4865_ = lean_ctor_get(v_a_4776_, 1);
v_lakeEnv_4866_ = lean_ctor_get(v_toContext_4865_, 0);
v_enableArtifactCache_x3f_4867_ = lean_ctor_get(v_lakeEnv_4866_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4867_) == 0)
{
lean_object* v_packages_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v_config_4871_; lean_object* v_enableArtifactCache_x3f_4872_; 
v_packages_4868_ = lean_ctor_get(v_toContext_4865_, 4);
v___x_4869_ = lean_unsigned_to_nat(0u);
v___x_4870_ = lean_array_fget_borrowed(v_packages_4868_, v___x_4869_);
v_config_4871_ = lean_ctor_get(v___x_4870_, 6);
v_enableArtifactCache_x3f_4872_ = lean_ctor_get(v_config_4871_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4872_) == 0)
{
lean_dec(v_val_4819_);
lean_dec_ref(v_pkg_4772_);
v_a_4828_ = v_a_4825_;
goto v___jp_4827_;
}
else
{
lean_object* v_val_4873_; uint8_t v___x_4874_; 
v_val_4873_ = lean_ctor_get(v_enableArtifactCache_x3f_4872_, 0);
v___x_4874_ = lean_unbox(v_val_4873_);
v_a_4832_ = v___x_4874_;
v_a_4833_ = v_a_4825_;
goto v___jp_4831_;
}
}
else
{
lean_object* v_val_4875_; uint8_t v___x_4876_; 
v_val_4875_ = lean_ctor_get(v_enableArtifactCache_x3f_4867_, 0);
v___x_4876_ = lean_unbox(v_val_4875_);
v_a_4832_ = v___x_4876_;
v_a_4833_ = v_a_4825_;
goto v___jp_4831_;
}
}
else
{
lean_object* v_val_4877_; uint8_t v___x_4878_; 
v_val_4877_ = lean_ctor_get(v_enableArtifactCache_x3f_4826_, 0);
v___x_4878_ = lean_unbox(v_val_4877_);
v_a_4832_ = v___x_4878_;
v_a_4833_ = v_a_4825_;
goto v___jp_4831_;
}
v___jp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = lean_box(0);
v___x_4830_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4824_, v___x_4829_, v___y_4769_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4828_);
lean_dec_ref(v___y_4769_);
v___y_4800_ = v___x_4830_;
goto v___jp_4799_;
}
v___jp_4831_:
{
if (v_a_4832_ == 0)
{
lean_dec(v_val_4819_);
lean_dec_ref(v_pkg_4772_);
v_a_4828_ = v_a_4833_;
goto v___jp_4827_;
}
else
{
lean_object* v_toContext_4834_; lean_object* v_log_4835_; uint8_t v_action_4836_; uint8_t v_wantsRebuild_4837_; lean_object* v_trace_4838_; lean_object* v_buildTime_4839_; lean_object* v_lakeCache_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; lean_object* v___x_4843_; 
v_toContext_4834_ = lean_ctor_get(v_a_4776_, 1);
v_log_4835_ = lean_ctor_get(v_a_4833_, 0);
v_action_4836_ = lean_ctor_get_uint8(v_a_4833_, sizeof(void*)*3);
v_wantsRebuild_4837_ = lean_ctor_get_uint8(v_a_4833_, sizeof(void*)*3 + 1);
v_trace_4838_ = lean_ctor_get(v_a_4833_, 1);
v_buildTime_4839_ = lean_ctor_get(v_a_4833_, 2);
v_lakeCache_4840_ = lean_ctor_get(v_toContext_4834_, 2);
v___x_4841_ = l_Lake_Package_cacheScope(v_pkg_4772_);
v___x_4842_ = 0;
lean_inc_ref(v_lakeCache_4840_);
v___x_4843_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4840_, v___x_4841_, v_inputHash_4770_, v_val_4819_, v___x_4820_, v___x_4820_, v___x_4842_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
lean_dec_ref_known(v___x_4843_, 1);
v___x_4844_ = lean_box(0);
v___x_4845_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4824_, v___x_4844_, v___y_4769_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4833_);
lean_dec_ref(v___y_4769_);
v___y_4800_ = v___x_4845_;
goto v___jp_4799_;
}
else
{
lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4861_; 
lean_inc(v_buildTime_4839_);
lean_inc_ref(v_trace_4838_);
lean_inc_ref(v_log_4835_);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_a_4833_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; lean_object* v_unused_4863_; lean_object* v_unused_4864_; 
v_unused_4862_ = lean_ctor_get(v_a_4833_, 2);
lean_dec(v_unused_4862_);
v_unused_4863_ = lean_ctor_get(v_a_4833_, 1);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_a_4833_, 0);
lean_dec(v_unused_4864_);
v___x_4847_ = v_a_4833_;
v_isShared_4848_ = v_isSharedCheck_4861_;
goto v_resetjp_4846_;
}
else
{
lean_dec(v_a_4833_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4861_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v_a_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; uint8_t v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v_a_4849_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4843_, 1);
v___x_4850_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4851_ = lean_io_error_to_string(v_a_4849_);
v___x_4852_ = lean_string_append(v___x_4850_, v___x_4851_);
lean_dec_ref(v___x_4851_);
v___x_4853_ = 2;
v___x_4854_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4854_, 0, v___x_4852_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*1, v___x_4853_);
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_array_push(v_log_4835_, v___x_4854_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4856_);
v___x_4858_ = v___x_4847_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4856_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_trace_4838_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_buildTime_4839_);
lean_ctor_set_uint8(v_reuseFailAlloc_4860_, sizeof(void*)*3, v_action_4836_);
lean_ctor_set_uint8(v_reuseFailAlloc_4860_, sizeof(void*)*3 + 1, v_wantsRebuild_4837_);
v___x_4858_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4824_, v___x_4855_, v___y_4769_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v___x_4858_);
lean_dec_ref(v___y_4769_);
v___y_4800_ = v___x_4859_;
goto v___jp_4799_;
}
}
}
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v_a_4880_; 
lean_dec(v_val_4819_);
lean_dec_ref(v_pkg_4772_);
lean_dec_ref(v___y_4769_);
v_a_4879_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4879_);
v_a_4880_ = lean_ctor_get(v___x_4822_, 1);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4822_, 2);
v_a_4784_ = v_a_4879_;
v_a_4785_ = v_a_4880_;
goto v___jp_4783_;
}
}
else
{
lean_dec(v_outputs_x3f_4817_);
lean_dec_ref(v_pkg_4772_);
lean_dec_ref(v___y_4769_);
v___y_4780_ = v_a_4777_;
goto v___jp_4779_;
}
}
}
else
{
lean_dec_ref(v_pkg_4772_);
lean_dec(v_savedTrace_4771_);
lean_dec_ref(v___y_4769_);
v___y_4780_ = v_a_4777_;
goto v___jp_4779_;
}
v___jp_4779_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_box(0);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
lean_ctor_set(v___x_4782_, 1, v___y_4780_);
return v___x_4782_;
}
v___jp_4783_:
{
lean_object* v_log_4786_; uint8_t v_action_4787_; uint8_t v_wantsRebuild_4788_; lean_object* v_trace_4789_; lean_object* v_buildTime_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4798_; 
v_log_4786_ = lean_ctor_get(v_a_4785_, 0);
v_action_4787_ = lean_ctor_get_uint8(v_a_4785_, sizeof(void*)*3);
v_wantsRebuild_4788_ = lean_ctor_get_uint8(v_a_4785_, sizeof(void*)*3 + 1);
v_trace_4789_ = lean_ctor_get(v_a_4785_, 1);
v_buildTime_4790_ = lean_ctor_get(v_a_4785_, 2);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_a_4785_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4792_ = v_a_4785_;
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_buildTime_4790_);
lean_inc(v_trace_4789_);
lean_inc(v_log_4786_);
lean_dec(v_a_4785_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = l_Array_shrink___redArg(v_log_4786_, v_a_4784_);
lean_dec(v_a_4784_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4794_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v_trace_4789_);
lean_ctor_set(v_reuseFailAlloc_4797_, 2, v_buildTime_4790_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*3, v_action_4787_);
lean_ctor_set_uint8(v_reuseFailAlloc_4797_, sizeof(void*)*3 + 1, v_wantsRebuild_4788_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
v___y_4780_ = v___x_4796_;
goto v___jp_4779_;
}
}
}
v___jp_4799_:
{
if (lean_obj_tag(v___y_4800_) == 0)
{
lean_object* v_a_4801_; 
v_a_4801_ = lean_ctor_get(v___y_4800_, 0);
if (lean_obj_tag(v_a_4801_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4810_; 
lean_inc_ref(v_a_4801_);
v_a_4802_ = lean_ctor_get(v___y_4800_, 1);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___y_4800_);
if (v_isSharedCheck_4810_ == 0)
{
lean_object* v_unused_4811_; 
v_unused_4811_ = lean_ctor_get(v___y_4800_, 0);
lean_dec(v_unused_4811_);
v___x_4804_ = v___y_4800_;
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___y_4800_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v_a_4806_; lean_object* v___x_4808_; 
v_a_4806_ = lean_ctor_get(v_a_4801_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v_a_4801_, 1);
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 0, v_a_4806_);
v___x_4808_ = v___x_4804_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4806_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_a_4802_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
else
{
lean_object* v_a_4812_; 
v_a_4812_ = lean_ctor_get(v___y_4800_, 1);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___y_4800_, 2);
v___y_4780_ = v_a_4812_;
goto v___jp_4779_;
}
}
else
{
lean_object* v_a_4813_; lean_object* v_a_4814_; 
v_a_4813_ = lean_ctor_get(v___y_4800_, 0);
lean_inc(v_a_4813_);
v_a_4814_ = lean_ctor_get(v___y_4800_, 1);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___y_4800_, 2);
v_a_4784_ = v_a_4813_;
v_a_4785_ = v_a_4814_;
goto v___jp_4783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4881_, lean_object* v___y_4882_, lean_object* v_inputHash_4883_, lean_object* v_savedTrace_4884_, lean_object* v_pkg_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
uint8_t v_exe_boxed_4892_; uint64_t v_inputHash_boxed_4893_; lean_object* v_res_4894_; 
v_exe_boxed_4892_ = lean_unbox(v_exe_4881_);
v_inputHash_boxed_4893_ = lean_unbox_uint64(v_inputHash_4883_);
lean_dec_ref(v_inputHash_4883_);
v_res_4894_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4892_, v___y_4882_, v_inputHash_boxed_4893_, v_savedTrace_4884_, v_pkg_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
lean_dec_ref(v_a_4889_);
lean_dec(v_a_4888_);
lean_dec(v_a_4887_);
lean_dec(v_a_4886_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4895_, size_t v_i_4896_, size_t v_stop_4897_, lean_object* v_b_4898_){
_start:
{
uint8_t v___x_4899_; 
v___x_4899_ = lean_usize_dec_eq(v_i_4896_, v_stop_4897_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; lean_object* v_message_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; size_t v___x_4905_; size_t v___x_4906_; 
v___x_4900_ = lean_array_uget_borrowed(v_as_4895_, v_i_4896_);
v_message_4901_ = lean_ctor_get(v___x_4900_, 0);
v___x_4902_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4903_ = lean_string_append(v_b_4898_, v___x_4902_);
v___x_4904_ = lean_string_append(v___x_4903_, v_message_4901_);
v___x_4905_ = ((size_t)1ULL);
v___x_4906_ = lean_usize_add(v_i_4896_, v___x_4905_);
v_i_4896_ = v___x_4906_;
v_b_4898_ = v___x_4904_;
goto _start;
}
else
{
return v_b_4898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4908_, lean_object* v_i_4909_, lean_object* v_stop_4910_, lean_object* v_b_4911_){
_start:
{
size_t v_i_boxed_4912_; size_t v_stop_boxed_4913_; lean_object* v_res_4914_; 
v_i_boxed_4912_ = lean_unbox_usize(v_i_4909_);
lean_dec(v_i_4909_);
v_stop_boxed_4913_ = lean_unbox_usize(v_stop_4910_);
lean_dec(v_stop_4910_);
v_res_4914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4908_, v_i_boxed_4912_, v_stop_boxed_4913_, v_b_4911_);
lean_dec_ref(v_as_4908_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4915_, lean_object* v___y_4916_, uint64_t v_inputHash_4917_, lean_object* v_pkg_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v_toContext_4925_; lean_object* v_log_4926_; uint8_t v_action_4927_; uint8_t v_wantsRebuild_4928_; lean_object* v_trace_4929_; lean_object* v_buildTime_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_5023_; 
v_toContext_4925_ = lean_ctor_get(v_a_4922_, 1);
v_log_4926_ = lean_ctor_get(v_a_4923_, 0);
v_action_4927_ = lean_ctor_get_uint8(v_a_4923_, sizeof(void*)*3);
v_wantsRebuild_4928_ = lean_ctor_get_uint8(v_a_4923_, sizeof(void*)*3 + 1);
v_trace_4929_ = lean_ctor_get(v_a_4923_, 1);
v_buildTime_4930_ = lean_ctor_get(v_a_4923_, 2);
v_isSharedCheck_5023_ = !lean_is_exclusive(v_a_4923_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_4932_ = v_a_4923_;
v_isShared_4933_ = v_isSharedCheck_5023_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_buildTime_4930_);
lean_inc(v_trace_4929_);
lean_inc(v_log_4926_);
lean_dec(v_a_4923_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_5023_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v_lakeCache_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v_lakeCache_4934_ = lean_ctor_get(v_toContext_4925_, 2);
v___x_4935_ = l_Lake_Package_cacheScope(v_pkg_4918_);
lean_inc_ref(v_lakeCache_4934_);
v___x_4936_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4934_, v___x_4935_, v_inputHash_4917_, v_log_4926_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_5010_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_a_4938_ = lean_ctor_get(v___x_4936_, 1);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_4940_ = v___x_4936_;
v_isShared_4941_ = v_isSharedCheck_5010_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_5010_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v_a_4938_);
v___x_4943_ = v___x_4932_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_4938_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_trace_4929_);
lean_ctor_set(v_reuseFailAlloc_5009_, 2, v_buildTime_4930_);
lean_ctor_set_uint8(v_reuseFailAlloc_5009_, sizeof(void*)*3, v_action_4927_);
lean_ctor_set_uint8(v_reuseFailAlloc_5009_, sizeof(void*)*3 + 1, v_wantsRebuild_4928_);
v___x_4943_ = v_reuseFailAlloc_5009_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
if (lean_obj_tag(v_a_4937_) == 1)
{
lean_object* v_val_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_5004_; 
v_val_4944_ = lean_ctor_get(v_a_4937_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_a_4937_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4946_ = v_a_4937_;
v_isShared_4947_ = v_isSharedCheck_5004_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_val_4944_);
lean_dec(v_a_4937_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_5004_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4948_; lean_object* v_r_4950_; lean_object* v___y_4951_; 
v___x_4948_ = l_Lake_resolveArtifactOutput(v_val_4944_, v_exe_4915_, v___y_4916_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v___x_4943_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4955_; lean_object* v_a_4956_; lean_object* v___x_4958_; 
v_a_4955_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4955_);
v_a_4956_ = lean_ctor_get(v___x_4948_, 1);
lean_inc(v_a_4956_);
lean_dec_ref_known(v___x_4948_, 2);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v_a_4955_);
v___x_4958_ = v___x_4946_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4955_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
v_r_4950_ = v___x_4958_;
v___y_4951_ = v_a_4956_;
goto v___jp_4949_;
}
}
else
{
lean_object* v_a_4960_; lean_object* v_a_4961_; lean_object* v_log_4962_; uint8_t v_action_4963_; uint8_t v_wantsRebuild_4964_; lean_object* v_trace_4965_; lean_object* v_buildTime_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5003_; 
lean_del_object(v___x_4946_);
v_a_4960_ = lean_ctor_get(v___x_4948_, 1);
lean_inc(v_a_4960_);
v_a_4961_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4948_, 2);
v_log_4962_ = lean_ctor_get(v_a_4960_, 0);
v_action_4963_ = lean_ctor_get_uint8(v_a_4960_, sizeof(void*)*3);
v_wantsRebuild_4964_ = lean_ctor_get_uint8(v_a_4960_, sizeof(void*)*3 + 1);
v_trace_4965_ = lean_ctor_get(v_a_4960_, 1);
v_buildTime_4966_ = lean_ctor_get(v_a_4960_, 2);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_a_4960_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4968_ = v_a_4960_;
v_isShared_4969_ = v_isSharedCheck_5003_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_buildTime_4966_);
lean_inc(v_trace_4965_);
lean_inc(v_log_4962_);
lean_dec(v_a_4960_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5003_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___y_4974_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; uint8_t v___x_4995_; 
v___x_4970_ = lean_array_get_size(v_log_4962_);
lean_inc(v_a_4961_);
v___x_4971_ = l_Array_extract___redArg(v_log_4962_, v_a_4961_, v___x_4970_);
v___x_4972_ = l_Array_shrink___redArg(v_log_4962_, v_a_4961_);
lean_dec(v_a_4961_);
v___x_4982_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4983_ = l_Lake_lowerHexUInt64(v_inputHash_4917_);
v___x_4984_ = lean_unsigned_to_nat(7u);
v___x_4985_ = lean_unsigned_to_nat(0u);
v___x_4986_ = lean_string_utf8_byte_size(v___x_4983_);
lean_inc_ref(v___x_4983_);
v___x_4987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4983_);
lean_ctor_set(v___x_4987_, 1, v___x_4985_);
lean_ctor_set(v___x_4987_, 2, v___x_4986_);
v___x_4988_ = l_String_Slice_Pos_nextn(v___x_4987_, v___x_4985_, v___x_4984_);
lean_dec_ref_known(v___x_4987_, 3);
v___x_4989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4983_);
lean_ctor_set(v___x_4989_, 1, v___x_4985_);
lean_ctor_set(v___x_4989_, 2, v___x_4988_);
v___x_4990_ = l_String_Slice_toString(v___x_4989_);
lean_dec_ref_known(v___x_4989_, 3);
v___x_4991_ = lean_string_append(v___x_4982_, v___x_4990_);
lean_dec_ref(v___x_4990_);
v___x_4992_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4993_ = lean_string_append(v___x_4991_, v___x_4992_);
v___x_4994_ = lean_array_get_size(v___x_4971_);
v___x_4995_ = lean_nat_dec_lt(v___x_4985_, v___x_4994_);
if (v___x_4995_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4974_ = v___x_4993_;
goto v___jp_4973_;
}
else
{
uint8_t v___x_4996_; 
v___x_4996_ = lean_nat_dec_le(v___x_4994_, v___x_4994_);
if (v___x_4996_ == 0)
{
if (v___x_4995_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4974_ = v___x_4993_;
goto v___jp_4973_;
}
else
{
size_t v___x_4997_; size_t v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = ((size_t)0ULL);
v___x_4998_ = lean_usize_of_nat(v___x_4994_);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4971_, v___x_4997_, v___x_4998_, v___x_4993_);
lean_dec_ref(v___x_4971_);
v___y_4974_ = v___x_4999_;
goto v___jp_4973_;
}
}
else
{
size_t v___x_5000_; size_t v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = ((size_t)0ULL);
v___x_5001_ = lean_usize_of_nat(v___x_4994_);
v___x_5002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4971_, v___x_5000_, v___x_5001_, v___x_4993_);
lean_dec_ref(v___x_4971_);
v___y_4974_ = v___x_5002_;
goto v___jp_4973_;
}
}
v___jp_4973_:
{
uint8_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4975_ = 2;
v___x_4976_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4976_, 0, v___y_4974_);
lean_ctor_set_uint8(v___x_4976_, sizeof(void*)*1, v___x_4975_);
v___x_4977_ = lean_array_push(v___x_4972_, v___x_4976_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_4977_);
v___x_4979_ = v___x_4968_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_trace_4965_);
lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_buildTime_4966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4981_, sizeof(void*)*3, v_action_4963_);
lean_ctor_set_uint8(v_reuseFailAlloc_4981_, sizeof(void*)*3 + 1, v_wantsRebuild_4964_);
v___x_4979_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_box(0);
v_r_4950_ = v___x_4980_;
v___y_4951_ = v___x_4979_;
goto v___jp_4949_;
}
}
}
}
v___jp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___y_4951_);
lean_ctor_set(v___x_4940_, 0, v_r_4950_);
v___x_4953_ = v___x_4940_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_r_4950_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v___y_4951_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
else
{
lean_object* v___x_5005_; lean_object* v___x_5007_; 
lean_dec(v_a_4937_);
lean_dec_ref(v___y_4916_);
v___x_5005_ = lean_box(0);
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_4943_);
lean_ctor_set(v___x_4940_, 0, v___x_5005_);
v___x_5007_ = v___x_4940_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_5005_);
lean_ctor_set(v_reuseFailAlloc_5008_, 1, v___x_4943_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
else
{
lean_object* v_a_5011_; lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v___y_4916_);
v_a_5011_ = lean_ctor_get(v___x_4936_, 0);
v_a_5012_ = lean_ctor_get(v___x_4936_, 1);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5014_ = v___x_4936_;
v_isShared_5015_ = v_isSharedCheck_5022_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_inc(v_a_5011_);
lean_dec(v___x_4936_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5022_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v_a_5012_);
v___x_5017_ = v___x_4932_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5012_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v_trace_4929_);
lean_ctor_set(v_reuseFailAlloc_5021_, 2, v_buildTime_4930_);
lean_ctor_set_uint8(v_reuseFailAlloc_5021_, sizeof(void*)*3, v_action_4927_);
lean_ctor_set_uint8(v_reuseFailAlloc_5021_, sizeof(void*)*3 + 1, v_wantsRebuild_4928_);
v___x_5017_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
lean_object* v___x_5019_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 1, v___x_5017_);
v___x_5019_ = v___x_5014_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5011_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_5024_, lean_object* v___y_5025_, lean_object* v_inputHash_5026_, lean_object* v_pkg_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
uint8_t v_exe_boxed_5034_; uint64_t v_inputHash_boxed_5035_; lean_object* v_res_5036_; 
v_exe_boxed_5034_ = lean_unbox(v_exe_5024_);
v_inputHash_boxed_5035_ = lean_unbox_uint64(v_inputHash_5026_);
lean_dec_ref(v_inputHash_5026_);
v_res_5036_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5034_, v___y_5025_, v_inputHash_boxed_5035_, v_pkg_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec(v_a_5029_);
lean_dec(v_a_5028_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5037_, uint64_t v_hash_5038_, lean_object* v_a_5039_, lean_object* v_val_5040_, lean_object* v_file_5041_, lean_object* v___x_5042_, uint8_t v_restore_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_a_5052_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___y_5058_; uint8_t v___y_5096_; uint8_t v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v_a_5117_; lean_object* v_val_5118_; lean_object* v_a_5119_; lean_object* v___y_5173_; lean_object* v_a_5179_; lean_object* v___y_5180_; lean_object* v___x_5182_; lean_object* v_a_5183_; 
lean_inc_ref(v_val_5040_);
lean_inc(v_a_5039_);
lean_inc_ref(v___y_5044_);
v___x_5182_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5037_, v___y_5044_, v_hash_5038_, v_a_5039_, v_val_5040_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
if (lean_obj_tag(v_a_5183_) == 1)
{
lean_object* v_a_5184_; lean_object* v_val_5185_; 
lean_dec_ref(v___y_5044_);
lean_dec_ref(v_val_5040_);
v_a_5184_ = lean_ctor_get(v___x_5182_, 1);
lean_inc(v_a_5184_);
lean_dec_ref(v___x_5182_);
v_val_5185_ = lean_ctor_get(v_a_5183_, 0);
lean_inc(v_val_5185_);
lean_dec_ref_known(v_a_5183_, 1);
v_a_5179_ = v_val_5185_;
v___y_5180_ = v_a_5184_;
goto v___jp_5178_;
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5187_; 
lean_dec(v_a_5183_);
v_a_5186_ = lean_ctor_get(v___x_5182_, 1);
lean_inc(v_a_5186_);
lean_dec_ref(v___x_5182_);
v___x_5187_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5037_, v___y_5044_, v_hash_5038_, v_val_5040_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v_a_5186_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
if (lean_obj_tag(v_a_5188_) == 1)
{
lean_object* v_a_5189_; lean_object* v_val_5190_; 
v_a_5189_ = lean_ctor_get(v___x_5187_, 1);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5187_, 2);
v_val_5190_ = lean_ctor_get(v_a_5188_, 0);
lean_inc(v_val_5190_);
lean_dec_ref_known(v_a_5188_, 1);
v_a_5179_ = v_val_5190_;
v___y_5180_ = v_a_5189_;
goto v___jp_5178_;
}
else
{
lean_object* v_a_5191_; 
lean_dec(v_a_5188_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_file_5041_);
lean_dec(v_a_5039_);
v_a_5191_ = lean_ctor_get(v___x_5187_, 1);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5187_, 2);
v_a_5052_ = v_a_5191_;
goto v___jp_5051_;
}
}
else
{
v___y_5173_ = v___x_5187_;
goto v___jp_5172_;
}
}
v___jp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_box(0);
v___x_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
lean_ctor_set(v___x_5054_, 1, v_a_5052_);
return v___x_5054_;
}
v___jp_5055_:
{
if (v_restore_5043_ == 0)
{
lean_object* v___x_5059_; 
lean_dec_ref(v___y_5057_);
lean_dec_ref(v_file_5041_);
v___x_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___y_5056_);
lean_ctor_set(v___x_5059_, 1, v___y_5058_);
return v___x_5059_;
}
else
{
lean_object* v_log_5060_; uint8_t v_action_5061_; uint8_t v_wantsRebuild_5062_; lean_object* v_trace_5063_; lean_object* v_buildTime_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v___y_5056_);
v_log_5060_ = lean_ctor_get(v___y_5058_, 0);
v_action_5061_ = lean_ctor_get_uint8(v___y_5058_, sizeof(void*)*3);
v_wantsRebuild_5062_ = lean_ctor_get_uint8(v___y_5058_, sizeof(void*)*3 + 1);
v_trace_5063_ = lean_ctor_get(v___y_5058_, 1);
v_buildTime_5064_ = lean_ctor_get(v___y_5058_, 2);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___y_5058_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5066_ = v___y_5058_;
v_isShared_5067_ = v_isSharedCheck_5094_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_buildTime_5064_);
lean_inc(v_trace_5063_);
lean_inc(v_log_5060_);
lean_dec(v___y_5058_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5094_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lake_restoreArtifact(v_file_5041_, v___y_5057_, v_exe_5037_, v_log_5060_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5081_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_a_5070_ = lean_ctor_get(v___x_5068_, 1);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5072_ = v___x_5068_;
v_isShared_5073_ = v_isSharedCheck_5081_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5081_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v_a_5070_);
v___x_5075_ = v___x_5066_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5070_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_trace_5063_);
lean_ctor_set(v_reuseFailAlloc_5080_, 2, v_buildTime_5064_);
lean_ctor_set_uint8(v_reuseFailAlloc_5080_, sizeof(void*)*3, v_action_5061_);
lean_ctor_set_uint8(v_reuseFailAlloc_5080_, sizeof(void*)*3 + 1, v_wantsRebuild_5062_);
v___x_5075_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5078_; 
v___x_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5076_, 0, v_a_5069_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 1, v___x_5075_);
lean_ctor_set(v___x_5072_, 0, v___x_5076_);
v___x_5078_ = v___x_5072_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v___x_5075_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_a_5082_; lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5093_; 
v_a_5082_ = lean_ctor_get(v___x_5068_, 0);
v_a_5083_ = lean_ctor_get(v___x_5068_, 1);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5085_ = v___x_5068_;
v_isShared_5086_ = v_isSharedCheck_5093_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_inc(v_a_5082_);
lean_dec(v___x_5068_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5093_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v_a_5083_);
v___x_5088_ = v___x_5066_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5083_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v_trace_5063_);
lean_ctor_set(v_reuseFailAlloc_5092_, 2, v_buildTime_5064_);
lean_ctor_set_uint8(v_reuseFailAlloc_5092_, sizeof(void*)*3, v_action_5061_);
lean_ctor_set_uint8(v_reuseFailAlloc_5092_, sizeof(void*)*3 + 1, v_wantsRebuild_5062_);
v___x_5088_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
lean_object* v___x_5090_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 1, v___x_5088_);
v___x_5090_ = v___x_5085_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5082_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
}
}
}
v___jp_5095_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5104_, 0, v___y_5103_);
v___x_5105_ = l_Lake_BuildMetadata_ofFetch(v_hash_5038_, v___x_5104_);
v___x_5106_ = l_Lake_BuildMetadata_writeFile(v___x_5042_, v___x_5105_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v___x_5107_; 
lean_dec_ref_known(v___x_5106_, 1);
v___x_5107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5107_, 0, v___y_5099_);
lean_ctor_set(v___x_5107_, 1, v___y_5100_);
lean_ctor_set(v___x_5107_, 2, v___y_5098_);
lean_ctor_set_uint8(v___x_5107_, sizeof(void*)*3, v___y_5096_);
lean_ctor_set_uint8(v___x_5107_, sizeof(void*)*3 + 1, v___y_5097_);
v___y_5056_ = v___y_5101_;
v___y_5057_ = v___y_5102_;
v___y_5058_ = v___x_5107_;
goto v___jp_5055_;
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v_file_5041_);
v_a_5108_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5106_, 1);
v___x_5109_ = lean_io_error_to_string(v_a_5108_);
v___x_5110_ = 3;
v___x_5111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5111_, 0, v___x_5109_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1, v___x_5110_);
v___x_5112_ = lean_array_get_size(v___y_5099_);
v___x_5113_ = lean_array_push(v___y_5099_, v___x_5111_);
v___x_5114_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
lean_ctor_set(v___x_5114_, 1, v___y_5100_);
lean_ctor_set(v___x_5114_, 2, v___y_5098_);
lean_ctor_set_uint8(v___x_5114_, sizeof(void*)*3, v___y_5096_);
lean_ctor_set_uint8(v___x_5114_, sizeof(void*)*3 + 1, v___y_5097_);
v___x_5115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5112_);
lean_ctor_set(v___x_5115_, 1, v___x_5114_);
return v___x_5115_;
}
}
v___jp_5116_:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5038_, v_a_5039_, v_a_5119_);
lean_dec(v_a_5039_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; uint8_t v___x_5122_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
v___x_5122_ = lean_unbox(v_a_5121_);
lean_dec(v_a_5121_);
if (v___x_5122_ == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5160_; 
v_a_5123_ = lean_ctor_get(v___x_5120_, 1);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5160_ == 0)
{
lean_object* v_unused_5161_; 
v_unused_5161_ = lean_ctor_get(v___x_5120_, 0);
lean_dec(v_unused_5161_);
v___x_5125_ = v___x_5120_;
v_isShared_5126_ = v_isSharedCheck_5160_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5120_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5160_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v_log_5127_; uint8_t v_action_5128_; uint8_t v_wantsRebuild_5129_; lean_object* v_trace_5130_; lean_object* v_buildTime_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5159_; 
v_log_5127_ = lean_ctor_get(v_a_5123_, 0);
v_action_5128_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*3);
v_wantsRebuild_5129_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*3 + 1);
v_trace_5130_ = lean_ctor_get(v_a_5123_, 1);
v_buildTime_5131_ = lean_ctor_get(v_a_5123_, 2);
v_isSharedCheck_5159_ = !lean_is_exclusive(v_a_5123_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5133_ = v_a_5123_;
v_isShared_5134_ = v_isSharedCheck_5159_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_buildTime_5131_);
lean_inc(v_trace_5130_);
lean_inc(v_log_5127_);
lean_dec(v_a_5123_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5159_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Lake_removeFileIfExists(v_file_5041_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_descr_5136_; uint64_t v_hash_5137_; lean_object* v_ext_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
lean_dec_ref_known(v___x_5135_, 1);
lean_del_object(v___x_5133_);
lean_del_object(v___x_5125_);
v_descr_5136_ = lean_ctor_get(v_val_5118_, 0);
v_hash_5137_ = lean_ctor_get_uint64(v_descr_5136_, sizeof(void*)*1);
v_ext_5138_ = lean_ctor_get(v_descr_5136_, 0);
v___x_5139_ = lean_string_utf8_byte_size(v_ext_5138_);
v___x_5140_ = lean_unsigned_to_nat(0u);
v___x_5141_ = lean_nat_dec_eq(v___x_5139_, v___x_5140_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5142_ = l_Lake_lowerHexUInt64(v_hash_5137_);
v___x_5143_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5144_ = lean_string_append(v___x_5142_, v___x_5143_);
v___x_5145_ = lean_string_append(v___x_5144_, v_ext_5138_);
v___y_5096_ = v_action_5128_;
v___y_5097_ = v_wantsRebuild_5129_;
v___y_5098_ = v_buildTime_5131_;
v___y_5099_ = v_log_5127_;
v___y_5100_ = v_trace_5130_;
v___y_5101_ = v_a_5117_;
v___y_5102_ = v_val_5118_;
v___y_5103_ = v___x_5145_;
goto v___jp_5095_;
}
else
{
lean_object* v___x_5146_; 
v___x_5146_ = l_Lake_lowerHexUInt64(v_hash_5137_);
v___y_5096_ = v_action_5128_;
v___y_5097_ = v_wantsRebuild_5129_;
v___y_5098_ = v_buildTime_5131_;
v___y_5099_ = v_log_5127_;
v___y_5100_ = v_trace_5130_;
v___y_5101_ = v_a_5117_;
v___y_5102_ = v_val_5118_;
v___y_5103_ = v___x_5146_;
goto v___jp_5095_;
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5154_; 
lean_dec_ref(v_val_5118_);
lean_dec(v_a_5117_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_file_5041_);
v_a_5147_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5135_, 1);
v___x_5148_ = lean_io_error_to_string(v_a_5147_);
v___x_5149_ = 3;
v___x_5150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5150_, 0, v___x_5148_);
lean_ctor_set_uint8(v___x_5150_, sizeof(void*)*1, v___x_5149_);
v___x_5151_ = lean_array_get_size(v_log_5127_);
v___x_5152_ = lean_array_push(v_log_5127_, v___x_5150_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5152_);
v___x_5154_ = v___x_5133_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5152_);
lean_ctor_set(v_reuseFailAlloc_5158_, 1, v_trace_5130_);
lean_ctor_set(v_reuseFailAlloc_5158_, 2, v_buildTime_5131_);
lean_ctor_set_uint8(v_reuseFailAlloc_5158_, sizeof(void*)*3, v_action_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5158_, sizeof(void*)*3 + 1, v_wantsRebuild_5129_);
v___x_5154_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
lean_object* v___x_5156_; 
if (v_isShared_5126_ == 0)
{
lean_ctor_set_tag(v___x_5125_, 1);
lean_ctor_set(v___x_5125_, 1, v___x_5154_);
lean_ctor_set(v___x_5125_, 0, v___x_5151_);
v___x_5156_ = v___x_5125_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5151_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v___x_5154_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
}
}
else
{
lean_object* v_a_5162_; 
lean_dec_ref(v___x_5042_);
v_a_5162_ = lean_ctor_get(v___x_5120_, 1);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5120_, 2);
v___y_5056_ = v_a_5117_;
v___y_5057_ = v_val_5118_;
v___y_5058_ = v_a_5162_;
goto v___jp_5055_;
}
}
else
{
lean_object* v_a_5163_; lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec_ref(v_val_5118_);
lean_dec(v_a_5117_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_file_5041_);
v_a_5163_ = lean_ctor_get(v___x_5120_, 0);
v_a_5164_ = lean_ctor_get(v___x_5120_, 1);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5120_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_inc(v_a_5163_);
lean_dec(v___x_5120_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5163_);
lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
v___jp_5172_:
{
if (lean_obj_tag(v___y_5173_) == 0)
{
lean_object* v_a_5174_; 
v_a_5174_ = lean_ctor_get(v___y_5173_, 0);
if (lean_obj_tag(v_a_5174_) == 1)
{
lean_object* v_a_5175_; lean_object* v_val_5176_; 
lean_inc_ref(v_a_5174_);
v_a_5175_ = lean_ctor_get(v___y_5173_, 1);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___y_5173_, 2);
v_val_5176_ = lean_ctor_get(v_a_5174_, 0);
lean_inc(v_val_5176_);
v_a_5117_ = v_a_5174_;
v_val_5118_ = v_val_5176_;
v_a_5119_ = v_a_5175_;
goto v___jp_5116_;
}
else
{
lean_object* v_a_5177_; 
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_file_5041_);
lean_dec(v_a_5039_);
v_a_5177_ = lean_ctor_get(v___y_5173_, 1);
lean_inc(v_a_5177_);
lean_dec_ref_known(v___y_5173_, 2);
v_a_5052_ = v_a_5177_;
goto v___jp_5051_;
}
}
else
{
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_file_5041_);
lean_dec(v_a_5039_);
return v___y_5173_;
}
}
v___jp_5178_:
{
lean_object* v___x_5181_; 
lean_inc_ref(v_a_5179_);
v___x_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5181_, 0, v_a_5179_);
v_a_5117_ = v___x_5181_;
v_val_5118_ = v_a_5179_;
v_a_5119_ = v___y_5180_;
goto v___jp_5116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5192_, lean_object* v_hash_5193_, lean_object* v_a_5194_, lean_object* v_val_5195_, lean_object* v_file_5196_, lean_object* v___x_5197_, lean_object* v_restore_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
uint8_t v_exe_boxed_5206_; uint64_t v_hash_boxed_5207_; uint8_t v_restore_boxed_5208_; lean_object* v_res_5209_; 
v_exe_boxed_5206_ = lean_unbox(v_exe_5192_);
v_hash_boxed_5207_ = lean_unbox_uint64(v_hash_5193_);
lean_dec_ref(v_hash_5193_);
v_restore_boxed_5208_ = lean_unbox(v_restore_5198_);
v_res_5209_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5206_, v_hash_boxed_5207_, v_a_5194_, v_val_5195_, v_file_5196_, v___x_5197_, v_restore_boxed_5208_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec(v___y_5200_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5210_, lean_object* v_file_5211_, lean_object* v_ext_5212_, uint8_t v_text_5213_, uint8_t v_exe_5214_, uint8_t v___y_5215_, lean_object* v_val_5216_, uint64_t v_hash_5217_, uint8_t v_a_5218_, lean_object* v_____r_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
uint8_t v___x_5227_; uint8_t v___x_5228_; 
v___x_5227_ = 1;
v___x_5228_ = l_Lake_instDecidableEqOutputStatus(v_a_5210_, v___x_5227_);
if (v___x_5228_ == 0)
{
lean_object* v_toContext_5229_; lean_object* v_log_5230_; uint8_t v_action_5231_; uint8_t v_wantsRebuild_5232_; lean_object* v_trace_5233_; lean_object* v_buildTime_5234_; lean_object* v_lakeCache_5235_; lean_object* v___x_5236_; 
v_toContext_5229_ = lean_ctor_get(v___y_5224_, 1);
v_log_5230_ = lean_ctor_get(v___y_5225_, 0);
v_action_5231_ = lean_ctor_get_uint8(v___y_5225_, sizeof(void*)*3);
v_wantsRebuild_5232_ = lean_ctor_get_uint8(v___y_5225_, sizeof(void*)*3 + 1);
v_trace_5233_ = lean_ctor_get(v___y_5225_, 1);
v_buildTime_5234_ = lean_ctor_get(v___y_5225_, 2);
v_lakeCache_5235_ = lean_ctor_get(v_toContext_5229_, 2);
lean_inc_ref(v_lakeCache_5235_);
v___x_5236_ = l_Lake_Cache_saveArtifact(v_lakeCache_5235_, v_file_5211_, v_ext_5212_, v_text_5213_, v_exe_5214_, v___y_5215_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5278_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5239_ = v___x_5236_;
v_isShared_5240_ = v_isSharedCheck_5278_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5236_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5278_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v_descr_5241_; uint64_t v_hash_5242_; lean_object* v_ext_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___y_5247_; lean_object* v___x_5270_; lean_object* v___x_5271_; uint8_t v___x_5272_; 
v_descr_5241_ = lean_ctor_get(v_a_5237_, 0);
v_hash_5242_ = lean_ctor_get_uint64(v_descr_5241_, sizeof(void*)*1);
v_ext_5243_ = lean_ctor_get(v_descr_5241_, 0);
v___x_5244_ = l_Lake_Package_cacheScope(v_val_5216_);
v___x_5245_ = lean_box(0);
v___x_5270_ = lean_string_utf8_byte_size(v_ext_5243_);
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = lean_nat_dec_eq(v___x_5270_, v___x_5271_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
v___x_5273_ = l_Lake_lowerHexUInt64(v_hash_5242_);
v___x_5274_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5275_ = lean_string_append(v___x_5273_, v___x_5274_);
v___x_5276_ = lean_string_append(v___x_5275_, v_ext_5243_);
v___y_5247_ = v___x_5276_;
goto v___jp_5246_;
}
else
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Lake_lowerHexUInt64(v_hash_5242_);
v___y_5247_ = v___x_5277_;
goto v___jp_5246_;
}
v___jp_5246_:
{
lean_object* v___x_5249_; 
if (v_isShared_5240_ == 0)
{
lean_ctor_set_tag(v___x_5239_, 3);
lean_ctor_set(v___x_5239_, 0, v___y_5247_);
v___x_5249_ = v___x_5239_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___y_5247_);
v___x_5249_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
lean_object* v___x_5250_; 
lean_inc_ref(v_lakeCache_5235_);
v___x_5250_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5235_, v___x_5244_, v_hash_5217_, v___x_5249_, v___x_5245_, v___x_5245_, v_a_5218_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v___x_5251_; 
lean_dec_ref_known(v___x_5250_, 1);
v___x_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5251_, 0, v_a_5237_);
lean_ctor_set(v___x_5251_, 1, v___y_5225_);
return v___x_5251_;
}
else
{
lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5265_; 
lean_inc(v_buildTime_5234_);
lean_inc_ref(v_trace_5233_);
lean_inc_ref(v_log_5230_);
lean_dec(v_a_5237_);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___y_5225_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; lean_object* v_unused_5267_; lean_object* v_unused_5268_; 
v_unused_5266_ = lean_ctor_get(v___y_5225_, 2);
lean_dec(v_unused_5266_);
v_unused_5267_ = lean_ctor_get(v___y_5225_, 1);
lean_dec(v_unused_5267_);
v_unused_5268_ = lean_ctor_get(v___y_5225_, 0);
lean_dec(v_unused_5268_);
v___x_5253_ = v___y_5225_;
v_isShared_5254_ = v_isSharedCheck_5265_;
goto v_resetjp_5252_;
}
else
{
lean_dec(v___y_5225_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5265_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v_a_5255_; lean_object* v___x_5256_; uint8_t v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5262_; 
v_a_5255_ = lean_ctor_get(v___x_5250_, 0);
lean_inc(v_a_5255_);
lean_dec_ref_known(v___x_5250_, 1);
v___x_5256_ = lean_io_error_to_string(v_a_5255_);
v___x_5257_ = 3;
v___x_5258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5258_, 0, v___x_5256_);
lean_ctor_set_uint8(v___x_5258_, sizeof(void*)*1, v___x_5257_);
v___x_5259_ = lean_array_get_size(v_log_5230_);
v___x_5260_ = lean_array_push(v_log_5230_, v___x_5258_);
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
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v_trace_5233_);
lean_ctor_set(v_reuseFailAlloc_5264_, 2, v_buildTime_5234_);
lean_ctor_set_uint8(v_reuseFailAlloc_5264_, sizeof(void*)*3, v_action_5231_);
lean_ctor_set_uint8(v_reuseFailAlloc_5264_, sizeof(void*)*3 + 1, v_wantsRebuild_5232_);
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
}
}
}
else
{
lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5292_; 
lean_inc(v_buildTime_5234_);
lean_inc_ref(v_trace_5233_);
lean_inc_ref(v_log_5230_);
lean_dec_ref(v_val_5216_);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___y_5225_);
if (v_isSharedCheck_5292_ == 0)
{
lean_object* v_unused_5293_; lean_object* v_unused_5294_; lean_object* v_unused_5295_; 
v_unused_5293_ = lean_ctor_get(v___y_5225_, 2);
lean_dec(v_unused_5293_);
v_unused_5294_ = lean_ctor_get(v___y_5225_, 1);
lean_dec(v_unused_5294_);
v_unused_5295_ = lean_ctor_get(v___y_5225_, 0);
lean_dec(v_unused_5295_);
v___x_5280_ = v___y_5225_;
v_isShared_5281_ = v_isSharedCheck_5292_;
goto v_resetjp_5279_;
}
else
{
lean_dec(v___y_5225_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5292_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v_a_5282_; lean_object* v___x_5283_; uint8_t v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5289_; 
v_a_5282_ = lean_ctor_get(v___x_5236_, 0);
lean_inc(v_a_5282_);
lean_dec_ref_known(v___x_5236_, 1);
v___x_5283_ = lean_io_error_to_string(v_a_5282_);
v___x_5284_ = 3;
v___x_5285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5285_, 0, v___x_5283_);
lean_ctor_set_uint8(v___x_5285_, sizeof(void*)*1, v___x_5284_);
v___x_5286_ = lean_array_get_size(v_log_5230_);
v___x_5287_ = lean_array_push(v_log_5230_, v___x_5285_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5287_);
v___x_5289_ = v___x_5280_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5287_);
lean_ctor_set(v_reuseFailAlloc_5291_, 1, v_trace_5233_);
lean_ctor_set(v_reuseFailAlloc_5291_, 2, v_buildTime_5234_);
lean_ctor_set_uint8(v_reuseFailAlloc_5291_, sizeof(void*)*3, v_action_5231_);
lean_ctor_set_uint8(v_reuseFailAlloc_5291_, sizeof(void*)*3 + 1, v_wantsRebuild_5232_);
v___x_5289_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
lean_object* v___x_5290_; 
v___x_5290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5286_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
return v___x_5290_;
}
}
}
}
else
{
lean_object* v___x_5296_; 
lean_dec_ref(v_val_5216_);
v___x_5296_ = l_Lake_computeArtifact___redArg(v_file_5211_, v_ext_5212_, v_text_5213_, v___y_5224_, v___y_5225_);
return v___x_5296_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5297_ = _args[0];
lean_object* v_file_5298_ = _args[1];
lean_object* v_ext_5299_ = _args[2];
lean_object* v_text_5300_ = _args[3];
lean_object* v_exe_5301_ = _args[4];
lean_object* v___y_5302_ = _args[5];
lean_object* v_val_5303_ = _args[6];
lean_object* v_hash_5304_ = _args[7];
lean_object* v_a_5305_ = _args[8];
lean_object* v_____r_5306_ = _args[9];
lean_object* v___y_5307_ = _args[10];
lean_object* v___y_5308_ = _args[11];
lean_object* v___y_5309_ = _args[12];
lean_object* v___y_5310_ = _args[13];
lean_object* v___y_5311_ = _args[14];
lean_object* v___y_5312_ = _args[15];
lean_object* v___y_5313_ = _args[16];
_start:
{
uint8_t v_a_299131__boxed_5314_; uint8_t v_text_boxed_5315_; uint8_t v_exe_boxed_5316_; uint8_t v___y_299132__boxed_5317_; uint64_t v_hash_boxed_5318_; uint8_t v_a_299134__boxed_5319_; lean_object* v_res_5320_; 
v_a_299131__boxed_5314_ = lean_unbox(v_a_5297_);
v_text_boxed_5315_ = lean_unbox(v_text_5300_);
v_exe_boxed_5316_ = lean_unbox(v_exe_5301_);
v___y_299132__boxed_5317_ = lean_unbox(v___y_5302_);
v_hash_boxed_5318_ = lean_unbox_uint64(v_hash_5304_);
lean_dec_ref(v_hash_5304_);
v_a_299134__boxed_5319_ = lean_unbox(v_a_5305_);
v_res_5320_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_299131__boxed_5314_, v_file_5298_, v_ext_5299_, v_text_boxed_5315_, v_exe_boxed_5316_, v___y_299132__boxed_5317_, v_val_5303_, v_hash_boxed_5318_, v_a_299134__boxed_5319_, v_____r_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5321_, lean_object* v_build_5322_, uint8_t v_text_5323_, lean_object* v_ext_5324_, uint8_t v_restore_5325_, uint8_t v_exe_5326_, uint8_t v_platformIndependent_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
lean_object* v_log_5335_; uint8_t v_action_5336_; uint8_t v_wantsRebuild_5337_; lean_object* v_trace_5338_; lean_object* v_buildTime_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5600_; 
v_log_5335_ = lean_ctor_get(v_a_5333_, 0);
v_action_5336_ = lean_ctor_get_uint8(v_a_5333_, sizeof(void*)*3);
v_wantsRebuild_5337_ = lean_ctor_get_uint8(v_a_5333_, sizeof(void*)*3 + 1);
v_trace_5338_ = lean_ctor_get(v_a_5333_, 1);
v_buildTime_5339_ = lean_ctor_get(v_a_5333_, 2);
v_isSharedCheck_5600_ = !lean_is_exclusive(v_a_5333_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5341_ = v_a_5333_;
v_isShared_5342_ = v_isSharedCheck_5600_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_buildTime_5339_);
lean_inc(v_trace_5338_);
lean_inc(v_log_5335_);
lean_dec(v_a_5333_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5600_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v_art_5346_; lean_object* v___y_5347_; lean_object* v___y_5363_; lean_object* v_log_5364_; uint8_t v_action_5365_; uint8_t v_wantsRebuild_5366_; lean_object* v_buildTime_5367_; lean_object* v___x_5373_; 
v___x_5343_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5321_);
v___x_5344_ = lean_string_append(v_file_5321_, v___x_5343_);
lean_inc_ref(v___x_5344_);
v___x_5373_ = l_Lake_readTraceFile(v___x_5344_, v_log_5335_);
if (lean_obj_tag(v___x_5373_) == 0)
{
if (lean_obj_tag(v_a_5329_) == 1)
{
lean_object* v_a_5374_; lean_object* v_a_5375_; lean_object* v_val_5376_; uint64_t v_hash_5377_; lean_object* v_mtime_5378_; uint8_t v___y_5380_; lean_object* v___y_5381_; lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5384_; uint8_t v___y_5385_; lean_object* v___y_5386_; lean_object* v___y_5387_; lean_object* v___y_5388_; lean_object* v_wsIdx_5392_; lean_object* v_config_5393_; lean_object* v_a_5395_; lean_object* v_a_5396_; lean_object* v___y_5426_; lean_object* v_enableArtifactCache_x3f_5429_; lean_object* v_restoreAllArtifacts_x3f_5430_; uint8_t v___y_5432_; lean_object* v___y_5433_; uint8_t v___y_5434_; uint8_t v___y_5473_; uint8_t v___y_5474_; uint8_t v_a_5475_; lean_object* v_a_5476_; uint8_t v___y_5478_; lean_object* v_a_5479_; uint8_t v___y_5496_; uint8_t v_a_5497_; lean_object* v_a_5498_; lean_object* v_a_5501_; uint8_t v_a_5533_; lean_object* v_a_5534_; lean_object* v___x_5550_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
lean_inc(v_a_5374_);
v_a_5375_ = lean_ctor_get(v___x_5373_, 1);
lean_inc(v_a_5375_);
lean_dec_ref_known(v___x_5373_, 2);
v_val_5376_ = lean_ctor_get(v_a_5329_, 0);
v_hash_5377_ = lean_ctor_get_uint64(v_trace_5338_, sizeof(void*)*3);
v_mtime_5378_ = lean_ctor_get(v_trace_5338_, 2);
v_wsIdx_5392_ = lean_ctor_get(v_val_5376_, 0);
v_config_5393_ = lean_ctor_get(v_val_5376_, 6);
v_enableArtifactCache_x3f_5429_ = lean_ctor_get(v_config_5393_, 24);
v_restoreAllArtifacts_x3f_5430_ = lean_ctor_get(v_config_5393_, 25);
lean_inc_ref(v_trace_5338_);
v___x_5550_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5550_, 0, v_a_5375_);
lean_ctor_set(v___x_5550_, 1, v_trace_5338_);
lean_ctor_set(v___x_5550_, 2, v_buildTime_5339_);
lean_ctor_set_uint8(v___x_5550_, sizeof(void*)*3, v_action_5336_);
lean_ctor_set_uint8(v___x_5550_, sizeof(void*)*3 + 1, v_wantsRebuild_5337_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5429_) == 0)
{
lean_object* v_toContext_5551_; lean_object* v_lakeEnv_5552_; lean_object* v_enableArtifactCache_x3f_5553_; 
v_toContext_5551_ = lean_ctor_get(v_a_5332_, 1);
v_lakeEnv_5552_ = lean_ctor_get(v_toContext_5551_, 0);
v_enableArtifactCache_x3f_5553_ = lean_ctor_get(v_lakeEnv_5552_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5553_) == 0)
{
lean_object* v_packages_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v_config_5557_; lean_object* v_enableArtifactCache_x3f_5558_; 
v_packages_5554_ = lean_ctor_get(v_toContext_5551_, 4);
v___x_5555_ = lean_unsigned_to_nat(0u);
v___x_5556_ = lean_array_fget_borrowed(v_packages_5554_, v___x_5555_);
v_config_5557_ = lean_ctor_get(v___x_5556_, 6);
v_enableArtifactCache_x3f_5558_ = lean_ctor_get(v_config_5557_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5558_) == 0)
{
v_a_5501_ = v___x_5550_;
goto v___jp_5500_;
}
else
{
lean_object* v_val_5559_; uint8_t v___x_5560_; 
v_val_5559_ = lean_ctor_get(v_enableArtifactCache_x3f_5558_, 0);
v___x_5560_ = lean_unbox(v_val_5559_);
v_a_5533_ = v___x_5560_;
v_a_5534_ = v___x_5550_;
goto v___jp_5532_;
}
}
else
{
lean_object* v_val_5561_; uint8_t v___x_5562_; 
v_val_5561_ = lean_ctor_get(v_enableArtifactCache_x3f_5553_, 0);
v___x_5562_ = lean_unbox(v_val_5561_);
v_a_5533_ = v___x_5562_;
v_a_5534_ = v___x_5550_;
goto v___jp_5532_;
}
}
else
{
lean_object* v_val_5563_; uint8_t v___x_5564_; 
v_val_5563_ = lean_ctor_get(v_enableArtifactCache_x3f_5429_, 0);
v___x_5564_ = lean_unbox(v_val_5563_);
v_a_5533_ = v___x_5564_;
v_a_5534_ = v___x_5550_;
goto v___jp_5532_;
}
v___jp_5379_:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
lean_dec_ref(v___y_5386_);
v___x_5389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5389_, 0, v___y_5388_);
v___x_5390_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5377_, v___x_5389_, v___y_5382_, v_platformIndependent_5327_);
v___x_5391_ = lean_st_ref_set(v___y_5387_, v___x_5390_);
v___y_5363_ = v___y_5383_;
v_log_5364_ = v___y_5384_;
v_action_5365_ = v___y_5380_;
v_wantsRebuild_5366_ = v___y_5385_;
v_buildTime_5367_ = v___y_5381_;
goto v___jp_5362_;
}
v___jp_5394_:
{
lean_object* v___x_5397_; uint8_t v___x_5398_; 
v___x_5397_ = lean_unsigned_to_nat(0u);
v___x_5398_ = lean_nat_dec_eq(v_wsIdx_5392_, v___x_5397_);
if (v___x_5398_ == 0)
{
lean_object* v_log_5399_; uint8_t v_action_5400_; uint8_t v_wantsRebuild_5401_; lean_object* v_buildTime_5402_; 
v_log_5399_ = lean_ctor_get(v_a_5396_, 0);
lean_inc_ref(v_log_5399_);
v_action_5400_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3);
v_wantsRebuild_5401_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3 + 1);
v_buildTime_5402_ = lean_ctor_get(v_a_5396_, 2);
lean_inc(v_buildTime_5402_);
lean_dec_ref(v_a_5396_);
v___y_5363_ = v_a_5395_;
v_log_5364_ = v_log_5399_;
v_action_5365_ = v_action_5400_;
v_wantsRebuild_5366_ = v_wantsRebuild_5401_;
v_buildTime_5367_ = v_buildTime_5402_;
goto v___jp_5362_;
}
else
{
lean_object* v_outputsRef_x3f_5403_; 
v_outputsRef_x3f_5403_ = lean_ctor_get(v_a_5332_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5403_) == 1)
{
lean_object* v_log_5404_; uint8_t v_action_5405_; uint8_t v_wantsRebuild_5406_; lean_object* v_trace_5407_; lean_object* v_buildTime_5408_; lean_object* v_val_5409_; lean_object* v___x_5410_; lean_object* v_descr_5411_; uint64_t v_hash_5412_; lean_object* v_ext_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; 
v_log_5404_ = lean_ctor_get(v_a_5396_, 0);
lean_inc_ref(v_log_5404_);
v_action_5405_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3);
v_wantsRebuild_5406_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3 + 1);
v_trace_5407_ = lean_ctor_get(v_a_5396_, 1);
lean_inc_ref(v_trace_5407_);
v_buildTime_5408_ = lean_ctor_get(v_a_5396_, 2);
lean_inc(v_buildTime_5408_);
lean_dec_ref(v_a_5396_);
v_val_5409_ = lean_ctor_get(v_outputsRef_x3f_5403_, 0);
v___x_5410_ = lean_st_ref_take(v_val_5409_);
v_descr_5411_ = lean_ctor_get(v_a_5395_, 0);
v_hash_5412_ = lean_ctor_get_uint64(v_descr_5411_, sizeof(void*)*1);
v_ext_5413_ = lean_ctor_get(v_descr_5411_, 0);
v___x_5414_ = lean_string_utf8_byte_size(v_ext_5413_);
v___x_5415_ = lean_nat_dec_eq(v___x_5414_, v___x_5397_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5416_ = l_Lake_lowerHexUInt64(v_hash_5412_);
v___x_5417_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5418_ = lean_string_append(v___x_5416_, v___x_5417_);
v___x_5419_ = lean_string_append(v___x_5418_, v_ext_5413_);
v___y_5380_ = v_action_5405_;
v___y_5381_ = v_buildTime_5408_;
v___y_5382_ = v___x_5410_;
v___y_5383_ = v_a_5395_;
v___y_5384_ = v_log_5404_;
v___y_5385_ = v_wantsRebuild_5406_;
v___y_5386_ = v_trace_5407_;
v___y_5387_ = v_val_5409_;
v___y_5388_ = v___x_5419_;
goto v___jp_5379_;
}
else
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Lake_lowerHexUInt64(v_hash_5412_);
v___y_5380_ = v_action_5405_;
v___y_5381_ = v_buildTime_5408_;
v___y_5382_ = v___x_5410_;
v___y_5383_ = v_a_5395_;
v___y_5384_ = v_log_5404_;
v___y_5385_ = v_wantsRebuild_5406_;
v___y_5386_ = v_trace_5407_;
v___y_5387_ = v_val_5409_;
v___y_5388_ = v___x_5420_;
goto v___jp_5379_;
}
}
else
{
lean_object* v_log_5421_; uint8_t v_action_5422_; uint8_t v_wantsRebuild_5423_; lean_object* v_buildTime_5424_; 
v_log_5421_ = lean_ctor_get(v_a_5396_, 0);
lean_inc_ref(v_log_5421_);
v_action_5422_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3);
v_wantsRebuild_5423_ = lean_ctor_get_uint8(v_a_5396_, sizeof(void*)*3 + 1);
v_buildTime_5424_ = lean_ctor_get(v_a_5396_, 2);
lean_inc(v_buildTime_5424_);
lean_dec_ref(v_a_5396_);
v___y_5363_ = v_a_5395_;
v_log_5364_ = v_log_5421_;
v_action_5365_ = v_action_5422_;
v_wantsRebuild_5366_ = v_wantsRebuild_5423_;
v_buildTime_5367_ = v_buildTime_5424_;
goto v___jp_5362_;
}
}
}
v___jp_5425_:
{
if (lean_obj_tag(v___y_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v_a_5428_; 
v_a_5427_ = lean_ctor_get(v___y_5426_, 0);
lean_inc(v_a_5427_);
v_a_5428_ = lean_ctor_get(v___y_5426_, 1);
lean_inc(v_a_5428_);
lean_dec_ref_known(v___y_5426_, 2);
v_a_5395_ = v_a_5427_;
v_a_5396_ = v_a_5428_;
goto v___jp_5394_;
}
else
{
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
return v___y_5426_;
}
}
v___jp_5431_:
{
lean_object* v___x_5435_; 
lean_inc_ref(v_a_5328_);
lean_inc_ref(v___x_5344_);
lean_inc_ref(v_file_5321_);
lean_inc(v_val_5376_);
lean_inc(v_a_5374_);
v___x_5435_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5326_, v_hash_5377_, v_a_5374_, v_val_5376_, v_file_5321_, v___x_5344_, v___y_5434_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v___y_5433_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
if (lean_obj_tag(v_a_5436_) == 1)
{
lean_object* v_a_5437_; lean_object* v_val_5438_; 
lean_dec(v_a_5374_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5437_ = lean_ctor_get(v___x_5435_, 1);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5435_, 2);
v_val_5438_ = lean_ctor_get(v_a_5436_, 0);
lean_inc(v_val_5438_);
lean_dec_ref_known(v_a_5436_, 1);
v_a_5395_ = v_val_5438_;
v_a_5396_ = v_a_5437_;
goto v___jp_5394_;
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5440_; 
lean_dec(v_a_5436_);
v_a_5439_ = lean_ctor_get(v___x_5435_, 1);
lean_inc(v_a_5439_);
lean_dec_ref_known(v___x_5435_, 2);
v___x_5440_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5328_, v_file_5321_, v_trace_5338_, v_a_5374_, v_mtime_5378_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5439_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v_a_5442_; uint8_t v___x_5443_; uint8_t v___x_5444_; uint8_t v___x_5445_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
v_a_5442_ = lean_ctor_get(v___x_5440_, 1);
lean_inc(v_a_5442_);
lean_dec_ref_known(v___x_5440_, 2);
v___x_5443_ = 0;
v___x_5444_ = lean_unbox(v_a_5441_);
v___x_5445_ = l_Lake_instDecidableEqOutputStatus(v___x_5444_, v___x_5443_);
if (v___x_5445_ == 0)
{
lean_object* v___x_5446_; uint8_t v___x_5447_; lean_object* v___x_5448_; 
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_build_5322_);
v___x_5446_ = lean_box(0);
v___x_5447_ = lean_unbox(v_a_5441_);
lean_dec(v_a_5441_);
lean_inc(v_val_5376_);
v___x_5448_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5447_, v_file_5321_, v_ext_5324_, v_text_5323_, v_exe_5326_, v___y_5434_, v_val_5376_, v_hash_5377_, v___y_5432_, v___x_5446_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5442_);
lean_dec_ref(v_a_5328_);
v___y_5426_ = v___x_5448_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5449_; 
lean_inc_ref(v_a_5328_);
lean_inc_ref(v___x_5344_);
lean_inc_ref(v_ext_5324_);
lean_inc_ref(v_file_5321_);
v___x_5449_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5321_, v_build_5322_, v_text_5323_, v_ext_5324_, v_trace_5338_, v___x_5344_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5442_);
lean_dec_ref(v_trace_5338_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; lean_object* v___x_5453_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 1);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 2);
v___x_5451_ = lean_box(0);
v___x_5452_ = lean_unbox(v_a_5441_);
lean_dec(v_a_5441_);
lean_inc(v_val_5376_);
v___x_5453_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5452_, v_file_5321_, v_ext_5324_, v_text_5323_, v_exe_5326_, v___y_5434_, v_val_5376_, v_hash_5377_, v___y_5432_, v___x_5451_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5450_);
lean_dec_ref(v_a_5328_);
v___y_5426_ = v___x_5453_;
goto v___jp_5425_;
}
else
{
lean_dec(v_a_5441_);
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_file_5321_);
return v___x_5449_;
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5454_ = lean_ctor_get(v___x_5440_, 0);
v_a_5455_ = lean_ctor_get(v___x_5440_, 1);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5440_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_inc(v_a_5454_);
lean_dec(v___x_5440_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5454_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec(v_a_5374_);
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5463_ = lean_ctor_get(v___x_5435_, 0);
v_a_5464_ = lean_ctor_get(v___x_5435_, 1);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5435_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_inc(v_a_5463_);
lean_dec(v___x_5435_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5463_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
v___jp_5472_:
{
if (v_restore_5325_ == 0)
{
v___y_5432_ = v___y_5473_;
v___y_5433_ = v_a_5476_;
v___y_5434_ = v_a_5475_;
goto v___jp_5431_;
}
else
{
v___y_5432_ = v___y_5473_;
v___y_5433_ = v_a_5476_;
v___y_5434_ = v___y_5474_;
goto v___jp_5431_;
}
}
v___jp_5477_:
{
lean_object* v___x_5480_; 
lean_inc_ref(v_a_5328_);
lean_inc_ref(v___x_5344_);
lean_inc_ref(v_file_5321_);
lean_inc(v_val_5376_);
v___x_5480_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5326_, v_hash_5377_, v_a_5374_, v_val_5376_, v_file_5321_, v___x_5344_, v___y_5478_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5479_);
if (lean_obj_tag(v___x_5480_) == 0)
{
lean_object* v_a_5481_; 
v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc(v_a_5481_);
if (lean_obj_tag(v_a_5481_) == 1)
{
lean_object* v_a_5482_; lean_object* v_val_5483_; 
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5482_ = lean_ctor_get(v___x_5480_, 1);
lean_inc(v_a_5482_);
lean_dec_ref_known(v___x_5480_, 2);
v_val_5483_ = lean_ctor_get(v_a_5481_, 0);
lean_inc(v_val_5483_);
lean_dec_ref_known(v_a_5481_, 1);
v_a_5395_ = v_val_5483_;
v_a_5396_ = v_a_5482_;
goto v___jp_5394_;
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5485_; 
lean_dec(v_a_5481_);
v_a_5484_ = lean_ctor_get(v___x_5480_, 1);
lean_inc(v_a_5484_);
lean_dec_ref_known(v___x_5480_, 2);
lean_inc_ref(v___x_5344_);
v___x_5485_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5321_, v_build_5322_, v_text_5323_, v_ext_5324_, v_trace_5338_, v___x_5344_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5484_);
lean_dec_ref(v_trace_5338_);
v___y_5426_ = v___x_5485_;
goto v___jp_5425_;
}
}
else
{
lean_object* v_a_5486_; lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5486_ = lean_ctor_get(v___x_5480_, 0);
v_a_5487_ = lean_ctor_get(v___x_5480_, 1);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5480_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_inc(v_a_5486_);
lean_dec(v___x_5480_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5486_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
v___jp_5495_:
{
if (v_a_5497_ == 0)
{
lean_object* v___x_5499_; 
lean_dec(v_a_5374_);
lean_inc_ref(v___x_5344_);
v___x_5499_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5321_, v_build_5322_, v_text_5323_, v_ext_5324_, v_trace_5338_, v___x_5344_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5498_);
lean_dec_ref(v_trace_5338_);
v___y_5426_ = v___x_5499_;
goto v___jp_5425_;
}
else
{
v___y_5478_ = v___y_5496_;
v_a_5479_ = v_a_5498_;
goto v___jp_5477_;
}
}
v___jp_5500_:
{
lean_object* v___x_5502_; 
lean_inc(v_a_5374_);
v___x_5502_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5328_, v_file_5321_, v_trace_5338_, v_a_5374_, v_mtime_5378_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5501_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v_a_5504_; uint8_t v___x_5505_; uint8_t v___x_5506_; uint8_t v___x_5507_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
v_a_5504_ = lean_ctor_get(v___x_5502_, 1);
lean_inc(v_a_5504_);
lean_dec_ref_known(v___x_5502_, 2);
v___x_5505_ = 0;
v___x_5506_ = lean_unbox(v_a_5503_);
lean_dec(v_a_5503_);
v___x_5507_ = l_Lake_instDecidableEqOutputStatus(v___x_5506_, v___x_5505_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; 
lean_dec(v_a_5374_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_build_5322_);
v___x_5508_ = l_Lake_computeArtifact___redArg(v_file_5321_, v_ext_5324_, v_text_5323_, v_a_5332_, v_a_5504_);
v___y_5426_ = v___x_5508_;
goto v___jp_5425_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5429_) == 0)
{
lean_object* v_toContext_5509_; lean_object* v_lakeEnv_5510_; lean_object* v_enableArtifactCache_x3f_5511_; 
v_toContext_5509_ = lean_ctor_get(v_a_5332_, 1);
v_lakeEnv_5510_ = lean_ctor_get(v_toContext_5509_, 0);
v_enableArtifactCache_x3f_5511_ = lean_ctor_get(v_lakeEnv_5510_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5511_) == 0)
{
lean_object* v_packages_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v_config_5515_; lean_object* v_enableArtifactCache_x3f_5516_; 
v_packages_5512_ = lean_ctor_get(v_toContext_5509_, 4);
v___x_5513_ = lean_unsigned_to_nat(0u);
v___x_5514_ = lean_array_fget_borrowed(v_packages_5512_, v___x_5513_);
v_config_5515_ = lean_ctor_get(v___x_5514_, 6);
v_enableArtifactCache_x3f_5516_ = lean_ctor_get(v_config_5515_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5516_) == 0)
{
v___y_5478_ = v___x_5507_;
v_a_5479_ = v_a_5504_;
goto v___jp_5477_;
}
else
{
lean_object* v_val_5517_; uint8_t v___x_5518_; 
v_val_5517_ = lean_ctor_get(v_enableArtifactCache_x3f_5516_, 0);
v___x_5518_ = lean_unbox(v_val_5517_);
v___y_5496_ = v___x_5507_;
v_a_5497_ = v___x_5518_;
v_a_5498_ = v_a_5504_;
goto v___jp_5495_;
}
}
else
{
lean_object* v_val_5519_; uint8_t v___x_5520_; 
v_val_5519_ = lean_ctor_get(v_enableArtifactCache_x3f_5511_, 0);
v___x_5520_ = lean_unbox(v_val_5519_);
v___y_5496_ = v___x_5507_;
v_a_5497_ = v___x_5520_;
v_a_5498_ = v_a_5504_;
goto v___jp_5495_;
}
}
else
{
lean_object* v_val_5521_; uint8_t v___x_5522_; 
v_val_5521_ = lean_ctor_get(v_enableArtifactCache_x3f_5429_, 0);
v___x_5522_ = lean_unbox(v_val_5521_);
v___y_5496_ = v___x_5507_;
v_a_5497_ = v___x_5522_;
v_a_5498_ = v_a_5504_;
goto v___jp_5495_;
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec(v_a_5374_);
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5523_ = lean_ctor_get(v___x_5502_, 0);
v_a_5524_ = lean_ctor_get(v___x_5502_, 1);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5502_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_inc(v_a_5523_);
lean_dec(v___x_5502_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5523_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_a_5524_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
v___jp_5532_:
{
if (v_a_5533_ == 0)
{
v_a_5501_ = v_a_5534_;
goto v___jp_5500_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5430_) == 0)
{
lean_object* v_toContext_5535_; lean_object* v_lakeEnv_5536_; lean_object* v_restoreAllArtifacts_x3f_5537_; 
v_toContext_5535_ = lean_ctor_get(v_a_5332_, 1);
v_lakeEnv_5536_ = lean_ctor_get(v_toContext_5535_, 0);
v_restoreAllArtifacts_x3f_5537_ = lean_ctor_get(v_lakeEnv_5536_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5537_) == 0)
{
lean_object* v_packages_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v_config_5541_; lean_object* v_restoreAllArtifacts_x3f_5542_; 
v_packages_5538_ = lean_ctor_get(v_toContext_5535_, 4);
v___x_5539_ = lean_unsigned_to_nat(0u);
v___x_5540_ = lean_array_fget_borrowed(v_packages_5538_, v___x_5539_);
v_config_5541_ = lean_ctor_get(v___x_5540_, 6);
v_restoreAllArtifacts_x3f_5542_ = lean_ctor_get(v_config_5541_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5542_) == 0)
{
uint8_t v___x_5543_; 
v___x_5543_ = 0;
v___y_5473_ = v_a_5533_;
v___y_5474_ = v_a_5533_;
v_a_5475_ = v___x_5543_;
v_a_5476_ = v_a_5534_;
goto v___jp_5472_;
}
else
{
lean_object* v_val_5544_; uint8_t v___x_5545_; 
v_val_5544_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5542_, 0);
v___x_5545_ = lean_unbox(v_val_5544_);
v___y_5473_ = v_a_5533_;
v___y_5474_ = v_a_5533_;
v_a_5475_ = v___x_5545_;
v_a_5476_ = v_a_5534_;
goto v___jp_5472_;
}
}
else
{
lean_object* v_val_5546_; uint8_t v___x_5547_; 
v_val_5546_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5537_, 0);
v___x_5547_ = lean_unbox(v_val_5546_);
v___y_5473_ = v_a_5533_;
v___y_5474_ = v_a_5533_;
v_a_5475_ = v___x_5547_;
v_a_5476_ = v_a_5534_;
goto v___jp_5472_;
}
}
else
{
lean_object* v_val_5548_; uint8_t v___x_5549_; 
v_val_5548_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5430_, 0);
v___x_5549_ = lean_unbox(v_val_5548_);
v___y_5473_ = v_a_5533_;
v___y_5474_ = v_a_5533_;
v_a_5475_ = v___x_5549_;
v_a_5476_ = v_a_5534_;
goto v___jp_5472_;
}
}
}
}
else
{
lean_object* v_a_5565_; lean_object* v_a_5566_; lean_object* v_mtime_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
lean_del_object(v___x_5341_);
v_a_5565_ = lean_ctor_get(v___x_5373_, 0);
lean_inc(v_a_5565_);
v_a_5566_ = lean_ctor_get(v___x_5373_, 1);
lean_inc(v_a_5566_);
lean_dec_ref_known(v___x_5373_, 2);
v_mtime_5567_ = lean_ctor_get(v_trace_5338_, 2);
lean_inc_ref(v_trace_5338_);
v___x_5568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5568_, 0, v_a_5566_);
lean_ctor_set(v___x_5568_, 1, v_trace_5338_);
lean_ctor_set(v___x_5568_, 2, v_buildTime_5339_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*3, v_action_5336_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*3 + 1, v_wantsRebuild_5337_);
v___x_5569_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5328_, v_file_5321_, v_trace_5338_, v_a_5565_, v_mtime_5567_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v___x_5568_);
if (lean_obj_tag(v___x_5569_) == 0)
{
lean_object* v_a_5570_; lean_object* v_a_5571_; uint8_t v___x_5572_; uint8_t v___x_5573_; uint8_t v___x_5574_; 
v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
lean_inc(v_a_5570_);
v_a_5571_ = lean_ctor_get(v___x_5569_, 1);
lean_inc(v_a_5571_);
lean_dec_ref_known(v___x_5569_, 2);
v___x_5572_ = 0;
v___x_5573_ = lean_unbox(v_a_5570_);
lean_dec(v_a_5570_);
v___x_5574_ = l_Lake_instDecidableEqOutputStatus(v___x_5573_, v___x_5572_);
if (v___x_5574_ == 0)
{
lean_object* v___x_5575_; 
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_build_5322_);
v___x_5575_ = l_Lake_computeArtifact___redArg(v_file_5321_, v_ext_5324_, v_text_5323_, v_a_5332_, v_a_5571_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v_a_5577_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc(v_a_5576_);
v_a_5577_ = lean_ctor_get(v___x_5575_, 1);
lean_inc(v_a_5577_);
lean_dec_ref_known(v___x_5575_, 2);
v_art_5346_ = v_a_5576_;
v___y_5347_ = v_a_5577_;
goto v___jp_5345_;
}
else
{
lean_dec_ref(v___x_5344_);
return v___x_5575_;
}
}
else
{
lean_object* v___x_5578_; 
lean_inc_ref(v___x_5344_);
v___x_5578_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5321_, v_build_5322_, v_text_5323_, v_ext_5324_, v_trace_5338_, v___x_5344_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5571_);
lean_dec_ref(v_trace_5338_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v_a_5580_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_a_5579_);
v_a_5580_ = lean_ctor_get(v___x_5578_, 1);
lean_inc(v_a_5580_);
lean_dec_ref_known(v___x_5578_, 2);
v_art_5346_ = v_a_5579_;
v___y_5347_ = v_a_5580_;
goto v___jp_5345_;
}
else
{
lean_dec_ref(v___x_5344_);
return v___x_5578_;
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5589_; 
lean_dec_ref(v___x_5344_);
lean_dec_ref(v_trace_5338_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5581_ = lean_ctor_get(v___x_5569_, 0);
v_a_5582_ = lean_ctor_get(v___x_5569_, 1);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5584_ = v___x_5569_;
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_inc(v_a_5581_);
lean_dec(v___x_5569_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
if (v_isShared_5585_ == 0)
{
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5581_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_a_5582_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
}
else
{
lean_object* v_a_5590_; lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5599_; 
lean_dec_ref(v___x_5344_);
lean_del_object(v___x_5341_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_ext_5324_);
lean_dec_ref(v_build_5322_);
lean_dec_ref(v_file_5321_);
v_a_5590_ = lean_ctor_get(v___x_5373_, 0);
v_a_5591_ = lean_ctor_get(v___x_5373_, 1);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5593_ = v___x_5373_;
v_isShared_5594_ = v_isSharedCheck_5599_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_inc(v_a_5590_);
lean_dec(v___x_5373_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5599_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5595_; lean_object* v___x_5597_; 
v___x_5595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5595_, 0, v_a_5591_);
lean_ctor_set(v___x_5595_, 1, v_trace_5338_);
lean_ctor_set(v___x_5595_, 2, v_buildTime_5339_);
lean_ctor_set_uint8(v___x_5595_, sizeof(void*)*3, v_action_5336_);
lean_ctor_set_uint8(v___x_5595_, sizeof(void*)*3 + 1, v_wantsRebuild_5337_);
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 1, v___x_5595_);
v___x_5597_ = v___x_5593_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5590_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v___x_5595_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
v___jp_5345_:
{
lean_object* v_log_5348_; uint8_t v_action_5349_; uint8_t v_wantsRebuild_5350_; lean_object* v_buildTime_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5360_; 
v_log_5348_ = lean_ctor_get(v___y_5347_, 0);
v_action_5349_ = lean_ctor_get_uint8(v___y_5347_, sizeof(void*)*3);
v_wantsRebuild_5350_ = lean_ctor_get_uint8(v___y_5347_, sizeof(void*)*3 + 1);
v_buildTime_5351_ = lean_ctor_get(v___y_5347_, 2);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___y_5347_);
if (v_isSharedCheck_5360_ == 0)
{
lean_object* v_unused_5361_; 
v_unused_5361_ = lean_ctor_get(v___y_5347_, 1);
lean_dec(v_unused_5361_);
v___x_5353_ = v___y_5347_;
v_isShared_5354_ = v_isSharedCheck_5360_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_buildTime_5351_);
lean_inc(v_log_5348_);
lean_dec(v___y_5347_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5360_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5355_ = l_Lake_Artifact_trace(v_art_5346_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5355_);
v___x_5357_ = v___x_5353_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_log_5348_);
lean_ctor_set(v_reuseFailAlloc_5359_, 1, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5359_, 2, v_buildTime_5351_);
lean_ctor_set_uint8(v_reuseFailAlloc_5359_, sizeof(void*)*3, v_action_5349_);
lean_ctor_set_uint8(v_reuseFailAlloc_5359_, sizeof(void*)*3 + 1, v_wantsRebuild_5350_);
v___x_5357_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; 
v___x_5358_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5346_, v___x_5344_, v___x_5357_);
lean_dec_ref(v___x_5344_);
return v___x_5358_;
}
}
}
v___jp_5362_:
{
lean_object* v___x_5368_; lean_object* v___x_5370_; 
v___x_5368_ = l_Lake_Artifact_trace(v___y_5363_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 2, v_buildTime_5367_);
lean_ctor_set(v___x_5341_, 1, v___x_5368_);
lean_ctor_set(v___x_5341_, 0, v_log_5364_);
v___x_5370_ = v___x_5341_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_log_5364_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v___x_5368_);
lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_buildTime_5367_);
v___x_5370_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
lean_object* v___x_5371_; 
lean_ctor_set_uint8(v___x_5370_, sizeof(void*)*3, v_action_5365_);
lean_ctor_set_uint8(v___x_5370_, sizeof(void*)*3 + 1, v_wantsRebuild_5366_);
v___x_5371_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5363_, v___x_5344_, v___x_5370_);
lean_dec_ref(v___x_5344_);
return v___x_5371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5601_, lean_object* v_build_5602_, lean_object* v_text_5603_, lean_object* v_ext_5604_, lean_object* v_restore_5605_, lean_object* v_exe_5606_, lean_object* v_platformIndependent_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
uint8_t v_text_boxed_5615_; uint8_t v_restore_boxed_5616_; uint8_t v_exe_boxed_5617_; uint8_t v_platformIndependent_boxed_5618_; lean_object* v_res_5619_; 
v_text_boxed_5615_ = lean_unbox(v_text_5603_);
v_restore_boxed_5616_ = lean_unbox(v_restore_5605_);
v_exe_boxed_5617_ = lean_unbox(v_exe_5606_);
v_platformIndependent_boxed_5618_ = lean_unbox(v_platformIndependent_5607_);
v_res_5619_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5601_, v_build_5602_, v_text_boxed_5615_, v_ext_5604_, v_restore_boxed_5616_, v_exe_boxed_5617_, v_platformIndependent_boxed_5618_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_);
lean_dec_ref(v_a_5612_);
lean_dec(v_a_5611_);
lean_dec(v_a_5610_);
lean_dec(v_a_5609_);
return v_res_5619_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5621_, lean_object* v_build_5622_, lean_object* v_file_5623_, uint8_t v_text_5624_, lean_object* v_depInfo_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v___x_5633_; 
lean_inc_ref(v___y_5630_);
lean_inc(v___y_5629_);
lean_inc(v___y_5628_);
lean_inc(v___y_5627_);
lean_inc_ref(v___y_5626_);
v___x_5633_ = lean_apply_7(v_extraDepTrace_5621_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_, lean_box(0));
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_object* v_a_5634_; lean_object* v_a_5635_; lean_object* v_log_5636_; uint8_t v_action_5637_; uint8_t v_wantsRebuild_5638_; lean_object* v_trace_5639_; lean_object* v_buildTime_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5671_; 
v_a_5634_ = lean_ctor_get(v___x_5633_, 1);
lean_inc(v_a_5634_);
v_a_5635_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_a_5635_);
lean_dec_ref_known(v___x_5633_, 2);
v_log_5636_ = lean_ctor_get(v_a_5634_, 0);
v_action_5637_ = lean_ctor_get_uint8(v_a_5634_, sizeof(void*)*3);
v_wantsRebuild_5638_ = lean_ctor_get_uint8(v_a_5634_, sizeof(void*)*3 + 1);
v_trace_5639_ = lean_ctor_get(v_a_5634_, 1);
v_buildTime_5640_ = lean_ctor_get(v_a_5634_, 2);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_a_5634_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5642_ = v_a_5634_;
v_isShared_5643_ = v_isSharedCheck_5671_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_buildTime_5640_);
lean_inc(v_trace_5639_);
lean_inc(v_log_5636_);
lean_dec(v_a_5634_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5671_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5644_; lean_object* v___x_5646_; 
v___x_5644_ = l_Lake_BuildTrace_mix(v_trace_5639_, v_a_5635_);
if (v_isShared_5643_ == 0)
{
lean_ctor_set(v___x_5642_, 1, v___x_5644_);
v___x_5646_ = v___x_5642_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_log_5636_);
lean_ctor_set(v_reuseFailAlloc_5670_, 1, v___x_5644_);
lean_ctor_set(v_reuseFailAlloc_5670_, 2, v_buildTime_5640_);
lean_ctor_set_uint8(v_reuseFailAlloc_5670_, sizeof(void*)*3, v_action_5637_);
lean_ctor_set_uint8(v_reuseFailAlloc_5670_, sizeof(void*)*3 + 1, v_wantsRebuild_5638_);
v___x_5646_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; uint8_t v___x_5649_; lean_object* v___x_5650_; 
v___x_5647_ = lean_apply_1(v_build_5622_, v_depInfo_5625_);
v___x_5648_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5649_ = 0;
v___x_5650_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5623_, v___x_5647_, v_text_5624_, v___x_5648_, v___x_5649_, v___x_5649_, v___x_5649_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___x_5646_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_object* v_a_5651_; lean_object* v_a_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5660_; 
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
v_a_5652_ = lean_ctor_get(v___x_5650_, 1);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5654_ = v___x_5650_;
v_isShared_5655_ = v_isSharedCheck_5660_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_a_5652_);
lean_inc(v_a_5651_);
lean_dec(v___x_5650_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5660_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v_path_5656_; lean_object* v___x_5658_; 
v_path_5656_ = lean_ctor_get(v_a_5651_, 1);
lean_inc_ref(v_path_5656_);
lean_dec(v_a_5651_);
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 0, v_path_5656_);
v___x_5658_ = v___x_5654_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_path_5656_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v_a_5652_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
else
{
lean_object* v_a_5661_; lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5669_; 
v_a_5661_ = lean_ctor_get(v___x_5650_, 0);
v_a_5662_ = lean_ctor_get(v___x_5650_, 1);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5664_ = v___x_5650_;
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_inc(v_a_5661_);
lean_dec(v___x_5650_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5667_; 
if (v_isShared_5665_ == 0)
{
v___x_5667_ = v___x_5664_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5661_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_a_5662_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v_a_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5680_; 
lean_dec_ref(v___y_5626_);
lean_dec(v_depInfo_5625_);
lean_dec_ref(v_file_5623_);
lean_dec_ref(v_build_5622_);
v_a_5672_ = lean_ctor_get(v___x_5633_, 0);
v_a_5673_ = lean_ctor_get(v___x_5633_, 1);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5633_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5675_ = v___x_5633_;
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_a_5673_);
lean_inc(v_a_5672_);
lean_dec(v___x_5633_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5678_; 
if (v_isShared_5676_ == 0)
{
v___x_5678_ = v___x_5675_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5672_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_a_5673_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5681_, lean_object* v_build_5682_, lean_object* v_file_5683_, lean_object* v_text_5684_, lean_object* v_depInfo_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
uint8_t v_text_boxed_5693_; lean_object* v_res_5694_; 
v_text_boxed_5693_ = lean_unbox(v_text_5684_);
v_res_5694_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5681_, v_build_5682_, v_file_5683_, v_text_boxed_5693_, v_depInfo_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec(v___y_5688_);
lean_dec(v___y_5687_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5695_, lean_object* v_dep_5696_, lean_object* v_build_5697_, lean_object* v_extraDepTrace_5698_, uint8_t v_text_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v___x_5707_; lean_object* v___f_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; uint8_t v___x_5711_; lean_object* v___x_5712_; 
v___x_5707_ = lean_box(v_text_5699_);
v___f_5708_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5708_, 0, v_extraDepTrace_5698_);
lean_closure_set(v___f_5708_, 1, v_build_5697_);
lean_closure_set(v___f_5708_, 2, v_file_5695_);
lean_closure_set(v___f_5708_, 3, v___x_5707_);
v___x_5709_ = l_Lake_instDataKindFilePath;
v___x_5710_ = lean_unsigned_to_nat(0u);
v___x_5711_ = 0;
v___x_5712_ = l_Lake_Job_mapM___redArg(v___x_5709_, v_dep_5696_, v___f_5708_, v___x_5710_, v___x_5711_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5713_, lean_object* v_dep_5714_, lean_object* v_build_5715_, lean_object* v_extraDepTrace_5716_, lean_object* v_text_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_){
_start:
{
uint8_t v_text_boxed_5725_; lean_object* v_res_5726_; 
v_text_boxed_5725_ = lean_unbox(v_text_5717_);
v_res_5726_ = l_Lake_buildFileAfterDep___redArg(v_file_5713_, v_dep_5714_, v_build_5715_, v_extraDepTrace_5716_, v_text_boxed_5725_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
lean_dec_ref(v_a_5723_);
lean_dec_ref(v_a_5722_);
lean_dec(v_a_5721_);
lean_dec(v_a_5720_);
lean_dec(v_a_5719_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5727_, lean_object* v_file_5728_, lean_object* v_dep_5729_, lean_object* v_build_5730_, lean_object* v_extraDepTrace_5731_, uint8_t v_text_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_){
_start:
{
lean_object* v___x_5740_; lean_object* v___f_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; uint8_t v___x_5744_; lean_object* v___x_5745_; 
v___x_5740_ = lean_box(v_text_5732_);
v___f_5741_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5741_, 0, v_extraDepTrace_5731_);
lean_closure_set(v___f_5741_, 1, v_build_5730_);
lean_closure_set(v___f_5741_, 2, v_file_5728_);
lean_closure_set(v___f_5741_, 3, v___x_5740_);
v___x_5742_ = l_Lake_instDataKindFilePath;
v___x_5743_ = lean_unsigned_to_nat(0u);
v___x_5744_ = 0;
v___x_5745_ = l_Lake_Job_mapM___redArg(v___x_5742_, v_dep_5729_, v___f_5741_, v___x_5743_, v___x_5744_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5746_, lean_object* v_file_5747_, lean_object* v_dep_5748_, lean_object* v_build_5749_, lean_object* v_extraDepTrace_5750_, lean_object* v_text_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_){
_start:
{
uint8_t v_text_boxed_5759_; lean_object* v_res_5760_; 
v_text_boxed_5759_ = lean_unbox(v_text_5751_);
v_res_5760_ = l_Lake_buildFileAfterDep(v_00_u03b1_5746_, v_file_5747_, v_dep_5748_, v_build_5749_, v_extraDepTrace_5750_, v_text_boxed_5759_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
lean_dec_ref(v_a_5757_);
lean_dec_ref(v_a_5756_);
lean_dec(v_a_5755_);
lean_dec(v_a_5754_);
lean_dec(v_a_5753_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5761_){
_start:
{
lean_object* v___x_5763_; 
v___x_5763_ = l_Lake_computeBinFileHash(v_info_5761_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_a_5764_; lean_object* v___x_5765_; 
v_a_5764_ = lean_ctor_get(v___x_5763_, 0);
lean_inc(v_a_5764_);
lean_dec_ref_known(v___x_5763_, 1);
v___x_5765_ = lean_io_metadata(v_info_5761_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5777_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5768_ = v___x_5765_;
v_isShared_5769_ = v_isSharedCheck_5777_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5765_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5777_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v_modified_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; uint64_t v___x_5773_; lean_object* v___x_5775_; 
v_modified_5770_ = lean_ctor_get(v_a_5766_, 1);
lean_inc_ref(v_modified_5770_);
lean_dec(v_a_5766_);
v___x_5771_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5772_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5772_, 0, v_info_5761_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
lean_ctor_set(v___x_5772_, 2, v_modified_5770_);
v___x_5773_ = lean_unbox_uint64(v_a_5764_);
lean_dec(v_a_5764_);
lean_ctor_set_uint64(v___x_5772_, sizeof(void*)*3, v___x_5773_);
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5772_);
v___x_5775_ = v___x_5768_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v___x_5772_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
lean_dec(v_a_5764_);
lean_dec_ref(v_info_5761_);
v_a_5778_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5780_ = v___x_5765_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5765_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec_ref(v_info_5761_);
v_a_5786_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5763_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5763_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5794_, lean_object* v_a_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5794_);
return v_res_5796_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
lean_object* v_log_5805_; uint8_t v_action_5806_; uint8_t v_wantsRebuild_5807_; lean_object* v_trace_5808_; lean_object* v_buildTime_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5829_; 
v_log_5805_ = lean_ctor_get(v___y_5803_, 0);
v_action_5806_ = lean_ctor_get_uint8(v___y_5803_, sizeof(void*)*3);
v_wantsRebuild_5807_ = lean_ctor_get_uint8(v___y_5803_, sizeof(void*)*3 + 1);
v_trace_5808_ = lean_ctor_get(v___y_5803_, 1);
v_buildTime_5809_ = lean_ctor_get(v___y_5803_, 2);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___y_5803_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5811_ = v___y_5803_;
v_isShared_5812_ = v_isSharedCheck_5829_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_buildTime_5809_);
lean_inc(v_trace_5808_);
lean_inc(v_log_5805_);
lean_dec(v___y_5803_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5829_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v___x_5813_; 
lean_inc_ref(v_path_5797_);
v___x_5813_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5797_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5816_; 
lean_dec_ref(v_trace_5808_);
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 1, v_a_5814_);
v___x_5816_ = v___x_5811_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_log_5805_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_a_5814_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_buildTime_5809_);
lean_ctor_set_uint8(v_reuseFailAlloc_5818_, sizeof(void*)*3, v_action_5806_);
lean_ctor_set_uint8(v_reuseFailAlloc_5818_, sizeof(void*)*3 + 1, v_wantsRebuild_5807_);
v___x_5816_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
lean_object* v___x_5817_; 
v___x_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5817_, 0, v_path_5797_);
lean_ctor_set(v___x_5817_, 1, v___x_5816_);
return v___x_5817_;
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5820_; uint8_t v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5826_; 
lean_dec_ref(v_path_5797_);
v_a_5819_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5819_);
lean_dec_ref_known(v___x_5813_, 1);
v___x_5820_ = lean_io_error_to_string(v_a_5819_);
v___x_5821_ = 3;
v___x_5822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5822_, 0, v___x_5820_);
lean_ctor_set_uint8(v___x_5822_, sizeof(void*)*1, v___x_5821_);
v___x_5823_ = lean_array_get_size(v_log_5805_);
v___x_5824_ = lean_array_push(v_log_5805_, v___x_5822_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 0, v___x_5824_);
v___x_5826_ = v___x_5811_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5824_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_trace_5808_);
lean_ctor_set(v_reuseFailAlloc_5828_, 2, v_buildTime_5809_);
lean_ctor_set_uint8(v_reuseFailAlloc_5828_, sizeof(void*)*3, v_action_5806_);
lean_ctor_set_uint8(v_reuseFailAlloc_5828_, sizeof(void*)*3 + 1, v_wantsRebuild_5807_);
v___x_5826_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5827_; 
v___x_5827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5823_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
return v___x_5827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec(v___y_5834_);
lean_dec(v___y_5833_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
lean_object* v___f_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___f_5847_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5847_, 0, v_path_5840_);
v___x_5848_ = l_Lake_instDataKindFilePath;
v___x_5849_ = lean_unsigned_to_nat(0u);
v___x_5850_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5851_ = l_Lake_Job_async___redArg(v___x_5848_, v___f_5847_, v___x_5849_, v___x_5850_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_){
_start:
{
lean_object* v_res_5859_; 
v_res_5859_ = l_Lake_inputBinFile___redArg(v_path_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_);
lean_dec_ref(v_a_5857_);
lean_dec(v_a_5856_);
lean_dec(v_a_5855_);
lean_dec(v_a_5854_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_, lean_object* v_a_5865_, lean_object* v_a_5866_){
_start:
{
lean_object* v___x_5868_; 
v___x_5868_ = l_Lake_inputBinFile___redArg(v_path_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_, v_a_5865_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lake_inputBinFile(v_path_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
lean_dec_ref(v_a_5875_);
lean_dec_ref(v_a_5874_);
lean_dec(v_a_5873_);
lean_dec(v_a_5872_);
lean_dec(v_a_5871_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5878_){
_start:
{
lean_object* v___x_5880_; 
v___x_5880_ = l_Lake_computeTextFileHash(v_info_5878_);
if (lean_obj_tag(v___x_5880_) == 0)
{
lean_object* v_a_5881_; lean_object* v___x_5882_; 
v_a_5881_ = lean_ctor_get(v___x_5880_, 0);
lean_inc(v_a_5881_);
lean_dec_ref_known(v___x_5880_, 1);
v___x_5882_ = lean_io_metadata(v_info_5878_);
if (lean_obj_tag(v___x_5882_) == 0)
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5894_; 
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5885_ = v___x_5882_;
v_isShared_5886_ = v_isSharedCheck_5894_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5882_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5894_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v_modified_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; uint64_t v___x_5890_; lean_object* v___x_5892_; 
v_modified_5887_ = lean_ctor_get(v_a_5883_, 1);
lean_inc_ref(v_modified_5887_);
lean_dec(v_a_5883_);
v___x_5888_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5889_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5889_, 0, v_info_5878_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
lean_ctor_set(v___x_5889_, 2, v_modified_5887_);
v___x_5890_ = lean_unbox_uint64(v_a_5881_);
lean_dec(v_a_5881_);
lean_ctor_set_uint64(v___x_5889_, sizeof(void*)*3, v___x_5890_);
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 0, v___x_5889_);
v___x_5892_ = v___x_5885_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5889_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec(v_a_5881_);
lean_dec_ref(v_info_5878_);
v_a_5895_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5882_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5882_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5910_; 
lean_dec_ref(v_info_5878_);
v_a_5903_ = lean_ctor_get(v___x_5880_, 0);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5880_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5905_ = v___x_5880_;
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
else
{
lean_inc(v_a_5903_);
lean_dec(v___x_5880_);
v___x_5905_ = lean_box(0);
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
v_resetjp_5904_:
{
lean_object* v___x_5908_; 
if (v_isShared_5906_ == 0)
{
v___x_5908_ = v___x_5905_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5911_, lean_object* v_a_5912_){
_start:
{
lean_object* v_res_5913_; 
v_res_5913_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5911_);
return v_res_5913_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_){
_start:
{
lean_object* v_log_5922_; uint8_t v_action_5923_; uint8_t v_wantsRebuild_5924_; lean_object* v_trace_5925_; lean_object* v_buildTime_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5946_; 
v_log_5922_ = lean_ctor_get(v___y_5920_, 0);
v_action_5923_ = lean_ctor_get_uint8(v___y_5920_, sizeof(void*)*3);
v_wantsRebuild_5924_ = lean_ctor_get_uint8(v___y_5920_, sizeof(void*)*3 + 1);
v_trace_5925_ = lean_ctor_get(v___y_5920_, 1);
v_buildTime_5926_ = lean_ctor_get(v___y_5920_, 2);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___y_5920_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5928_ = v___y_5920_;
v_isShared_5929_ = v_isSharedCheck_5946_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_buildTime_5926_);
lean_inc(v_trace_5925_);
lean_inc(v_log_5922_);
lean_dec(v___y_5920_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5946_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5930_; 
lean_inc_ref(v_path_5914_);
v___x_5930_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5914_);
if (lean_obj_tag(v___x_5930_) == 0)
{
lean_object* v_a_5931_; lean_object* v___x_5933_; 
lean_dec_ref(v_trace_5925_);
v_a_5931_ = lean_ctor_get(v___x_5930_, 0);
lean_inc(v_a_5931_);
lean_dec_ref_known(v___x_5930_, 1);
if (v_isShared_5929_ == 0)
{
lean_ctor_set(v___x_5928_, 1, v_a_5931_);
v___x_5933_ = v___x_5928_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_log_5922_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v_a_5931_);
lean_ctor_set(v_reuseFailAlloc_5935_, 2, v_buildTime_5926_);
lean_ctor_set_uint8(v_reuseFailAlloc_5935_, sizeof(void*)*3, v_action_5923_);
lean_ctor_set_uint8(v_reuseFailAlloc_5935_, sizeof(void*)*3 + 1, v_wantsRebuild_5924_);
v___x_5933_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_object* v___x_5934_; 
v___x_5934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5934_, 0, v_path_5914_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
return v___x_5934_;
}
}
else
{
lean_object* v_a_5936_; lean_object* v___x_5937_; uint8_t v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5943_; 
lean_dec_ref(v_path_5914_);
v_a_5936_ = lean_ctor_get(v___x_5930_, 0);
lean_inc(v_a_5936_);
lean_dec_ref_known(v___x_5930_, 1);
v___x_5937_ = lean_io_error_to_string(v_a_5936_);
v___x_5938_ = 3;
v___x_5939_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5937_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5938_);
v___x_5940_ = lean_array_get_size(v_log_5922_);
v___x_5941_ = lean_array_push(v_log_5922_, v___x_5939_);
if (v_isShared_5929_ == 0)
{
lean_ctor_set(v___x_5928_, 0, v___x_5941_);
v___x_5943_ = v___x_5928_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v___x_5941_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v_trace_5925_);
lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_buildTime_5926_);
lean_ctor_set_uint8(v_reuseFailAlloc_5945_, sizeof(void*)*3, v_action_5923_);
lean_ctor_set_uint8(v_reuseFailAlloc_5945_, sizeof(void*)*3 + 1, v_wantsRebuild_5924_);
v___x_5943_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
lean_object* v___x_5944_; 
v___x_5944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5940_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
return v___x_5944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v___f_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___f_5963_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5963_, 0, v_path_5956_);
v___x_5964_ = l_Lake_instDataKindFilePath;
v___x_5965_ = lean_unsigned_to_nat(0u);
v___x_5966_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5967_ = l_Lake_Job_async___redArg(v___x_5964_, v___f_5963_, v___x_5965_, v___x_5966_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
return v___x_5967_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_){
_start:
{
lean_object* v_res_5975_; 
v_res_5975_ = l_Lake_inputTextFile___redArg(v_path_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec(v_a_5971_);
lean_dec(v_a_5970_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_){
_start:
{
lean_object* v___x_5984_; 
v___x_5984_ = l_Lake_inputTextFile___redArg(v_path_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_);
return v___x_5984_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_){
_start:
{
lean_object* v_res_5993_; 
v_res_5993_ = l_Lake_inputTextFile(v_path_5985_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
lean_dec_ref(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec(v_a_5988_);
lean_dec(v_a_5987_);
return v_res_5993_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5994_, uint8_t v_text_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
if (v_text_5995_ == 0)
{
lean_object* v___x_6002_; 
v___x_6002_ = l_Lake_inputBinFile___redArg(v_path_5994_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
return v___x_6002_;
}
else
{
lean_object* v___x_6003_; 
v___x_6003_ = l_Lake_inputTextFile___redArg(v_path_5994_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
return v___x_6003_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_6004_, lean_object* v_text_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_){
_start:
{
uint8_t v_text_boxed_6012_; lean_object* v_res_6013_; 
v_text_boxed_6012_ = lean_unbox(v_text_6005_);
v_res_6013_ = l_Lake_inputFile___redArg(v_path_6004_, v_text_boxed_6012_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
lean_dec_ref(v_a_6010_);
lean_dec(v_a_6009_);
lean_dec(v_a_6008_);
lean_dec(v_a_6007_);
return v_res_6013_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_6014_, uint8_t v_text_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_){
_start:
{
if (v_text_6015_ == 0)
{
lean_object* v___x_6023_; 
v___x_6023_ = l_Lake_inputBinFile___redArg(v_path_6014_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
return v___x_6023_;
}
else
{
lean_object* v___x_6024_; 
v___x_6024_ = l_Lake_inputTextFile___redArg(v_path_6014_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
return v___x_6024_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_6025_, lean_object* v_text_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_){
_start:
{
uint8_t v_text_boxed_6034_; lean_object* v_res_6035_; 
v_text_boxed_6034_ = lean_unbox(v_text_6026_);
v_res_6035_ = l_Lake_inputFile(v_path_6025_, v_text_boxed_6034_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_, v_a_6031_, v_a_6032_);
lean_dec_ref(v_a_6032_);
lean_dec_ref(v_a_6031_);
lean_dec(v_a_6030_);
lean_dec(v_a_6029_);
lean_dec(v_a_6028_);
return v_res_6035_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6036_){
_start:
{
uint8_t v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6038_ = 1;
v___x_6039_ = lean_box(v___x_6038_);
v___x_6040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v_res_6043_; 
v_res_6043_ = l_Lake_inputDir___lam__0(v_x_6041_);
lean_dec_ref(v_x_6041_);
return v_res_6043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6044_, lean_object* v_as_6045_, size_t v_i_6046_, size_t v_stop_6047_, lean_object* v_b_6048_, lean_object* v___y_6049_){
_start:
{
lean_object* v_a_6052_; lean_object* v_a_6053_; uint8_t v___x_6057_; 
v___x_6057_ = lean_usize_dec_eq(v_i_6046_, v_stop_6047_);
if (v___x_6057_ == 0)
{
lean_object* v___x_6058_; uint8_t v___x_6059_; 
v___x_6058_ = lean_array_uget_borrowed(v_as_6045_, v_i_6046_);
v___x_6059_ = l_System_FilePath_isDir(v___x_6058_);
if (v___x_6059_ == 0)
{
lean_object* v___x_6060_; uint8_t v___x_6061_; 
lean_inc_ref(v_filter_6044_);
lean_inc(v___x_6058_);
v___x_6060_ = lean_apply_1(v_filter_6044_, v___x_6058_);
v___x_6061_ = lean_unbox(v___x_6060_);
if (v___x_6061_ == 0)
{
v_a_6052_ = v_b_6048_;
v_a_6053_ = v___y_6049_;
goto v___jp_6051_;
}
else
{
lean_object* v___x_6062_; 
lean_inc(v___x_6058_);
v___x_6062_ = lean_array_push(v_b_6048_, v___x_6058_);
v_a_6052_ = v___x_6062_;
v_a_6053_ = v___y_6049_;
goto v___jp_6051_;
}
}
else
{
v_a_6052_ = v_b_6048_;
v_a_6053_ = v___y_6049_;
goto v___jp_6051_;
}
}
else
{
lean_object* v___x_6063_; 
lean_dec_ref(v_filter_6044_);
v___x_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6063_, 0, v_b_6048_);
lean_ctor_set(v___x_6063_, 1, v___y_6049_);
return v___x_6063_;
}
v___jp_6051_:
{
size_t v___x_6054_; size_t v___x_6055_; 
v___x_6054_ = ((size_t)1ULL);
v___x_6055_ = lean_usize_add(v_i_6046_, v___x_6054_);
v_i_6046_ = v___x_6055_;
v_b_6048_ = v_a_6052_;
v___y_6049_ = v_a_6053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6064_, lean_object* v_as_6065_, lean_object* v_i_6066_, lean_object* v_stop_6067_, lean_object* v_b_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_){
_start:
{
size_t v_i_boxed_6071_; size_t v_stop_boxed_6072_; lean_object* v_res_6073_; 
v_i_boxed_6071_ = lean_unbox_usize(v_i_6066_);
lean_dec(v_i_6066_);
v_stop_boxed_6072_ = lean_unbox_usize(v_stop_6067_);
lean_dec(v_stop_6067_);
v_res_6073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6064_, v_as_6065_, v_i_boxed_6071_, v_stop_boxed_6072_, v_b_6068_, v___y_6069_);
lean_dec_ref(v_as_6065_);
return v_res_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6074_, lean_object* v_pivot_6075_, lean_object* v_as_6076_, lean_object* v_i_6077_, lean_object* v_k_6078_){
_start:
{
uint8_t v___x_6079_; 
v___x_6079_ = lean_nat_dec_lt(v_k_6078_, v_hi_6074_);
if (v___x_6079_ == 0)
{
lean_object* v___x_6080_; lean_object* v___x_6081_; 
lean_dec(v_k_6078_);
v___x_6080_ = lean_array_fswap(v_as_6076_, v_i_6077_, v_hi_6074_);
v___x_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6081_, 0, v_i_6077_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
return v___x_6081_;
}
else
{
lean_object* v___x_6082_; uint8_t v___x_6083_; 
v___x_6082_ = lean_array_fget_borrowed(v_as_6076_, v_k_6078_);
v___x_6083_ = lean_string_dec_lt(v___x_6082_, v_pivot_6075_);
if (v___x_6083_ == 0)
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6084_ = lean_unsigned_to_nat(1u);
v___x_6085_ = lean_nat_add(v_k_6078_, v___x_6084_);
lean_dec(v_k_6078_);
v_k_6078_ = v___x_6085_;
goto _start;
}
else
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6087_ = lean_array_fswap(v_as_6076_, v_i_6077_, v_k_6078_);
v___x_6088_ = lean_unsigned_to_nat(1u);
v___x_6089_ = lean_nat_add(v_i_6077_, v___x_6088_);
lean_dec(v_i_6077_);
v___x_6090_ = lean_nat_add(v_k_6078_, v___x_6088_);
lean_dec(v_k_6078_);
v_as_6076_ = v___x_6087_;
v_i_6077_ = v___x_6089_;
v_k_6078_ = v___x_6090_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6092_, lean_object* v_pivot_6093_, lean_object* v_as_6094_, lean_object* v_i_6095_, lean_object* v_k_6096_){
_start:
{
lean_object* v_res_6097_; 
v_res_6097_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6092_, v_pivot_6093_, v_as_6094_, v_i_6095_, v_k_6096_);
lean_dec_ref(v_pivot_6093_);
lean_dec(v_hi_6092_);
return v_res_6097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6098_, lean_object* v_as_6099_, lean_object* v_lo_6100_, lean_object* v_hi_6101_){
_start:
{
lean_object* v___y_6103_; uint8_t v___x_6113_; 
v___x_6113_ = lean_nat_dec_lt(v_lo_6100_, v_hi_6101_);
if (v___x_6113_ == 0)
{
lean_dec(v_lo_6100_);
return v_as_6099_;
}
else
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v_mid_6116_; lean_object* v___y_6118_; lean_object* v___y_6124_; lean_object* v___x_6129_; lean_object* v___x_6130_; uint8_t v___x_6131_; 
v___x_6114_ = lean_nat_add(v_lo_6100_, v_hi_6101_);
v___x_6115_ = lean_unsigned_to_nat(1u);
v_mid_6116_ = lean_nat_shiftr(v___x_6114_, v___x_6115_);
lean_dec(v___x_6114_);
v___x_6129_ = lean_array_fget_borrowed(v_as_6099_, v_mid_6116_);
v___x_6130_ = lean_array_fget_borrowed(v_as_6099_, v_lo_6100_);
v___x_6131_ = lean_string_dec_lt(v___x_6129_, v___x_6130_);
if (v___x_6131_ == 0)
{
v___y_6124_ = v_as_6099_;
goto v___jp_6123_;
}
else
{
lean_object* v___x_6132_; 
v___x_6132_ = lean_array_fswap(v_as_6099_, v_lo_6100_, v_mid_6116_);
v___y_6124_ = v___x_6132_;
goto v___jp_6123_;
}
v___jp_6117_:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; uint8_t v___x_6121_; 
v___x_6119_ = lean_array_fget_borrowed(v___y_6118_, v_mid_6116_);
v___x_6120_ = lean_array_fget_borrowed(v___y_6118_, v_hi_6101_);
v___x_6121_ = lean_string_dec_lt(v___x_6119_, v___x_6120_);
if (v___x_6121_ == 0)
{
lean_dec(v_mid_6116_);
v___y_6103_ = v___y_6118_;
goto v___jp_6102_;
}
else
{
lean_object* v___x_6122_; 
v___x_6122_ = lean_array_fswap(v___y_6118_, v_mid_6116_, v_hi_6101_);
lean_dec(v_mid_6116_);
v___y_6103_ = v___x_6122_;
goto v___jp_6102_;
}
}
v___jp_6123_:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; uint8_t v___x_6127_; 
v___x_6125_ = lean_array_fget_borrowed(v___y_6124_, v_hi_6101_);
v___x_6126_ = lean_array_fget_borrowed(v___y_6124_, v_lo_6100_);
v___x_6127_ = lean_string_dec_lt(v___x_6125_, v___x_6126_);
if (v___x_6127_ == 0)
{
v___y_6118_ = v___y_6124_;
goto v___jp_6117_;
}
else
{
lean_object* v___x_6128_; 
v___x_6128_ = lean_array_fswap(v___y_6124_, v_lo_6100_, v_hi_6101_);
v___y_6118_ = v___x_6128_;
goto v___jp_6117_;
}
}
}
v___jp_6102_:
{
lean_object* v_pivot_6104_; lean_object* v___x_6105_; lean_object* v_fst_6106_; lean_object* v_snd_6107_; uint8_t v___x_6108_; 
v_pivot_6104_ = lean_array_fget(v___y_6103_, v_hi_6101_);
lean_inc_n(v_lo_6100_, 2);
v___x_6105_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6101_, v_pivot_6104_, v___y_6103_, v_lo_6100_, v_lo_6100_);
lean_dec(v_pivot_6104_);
v_fst_6106_ = lean_ctor_get(v___x_6105_, 0);
lean_inc(v_fst_6106_);
v_snd_6107_ = lean_ctor_get(v___x_6105_, 1);
lean_inc(v_snd_6107_);
lean_dec_ref(v___x_6105_);
v___x_6108_ = lean_nat_dec_le(v_hi_6101_, v_fst_6106_);
if (v___x_6108_ == 0)
{
lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; 
v___x_6109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6098_, v_snd_6107_, v_lo_6100_, v_fst_6106_);
v___x_6110_ = lean_unsigned_to_nat(1u);
v___x_6111_ = lean_nat_add(v_fst_6106_, v___x_6110_);
lean_dec(v_fst_6106_);
v_as_6099_ = v___x_6109_;
v_lo_6100_ = v___x_6111_;
goto _start;
}
else
{
lean_dec(v_fst_6106_);
lean_dec(v_lo_6100_);
return v_snd_6107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6133_, lean_object* v_as_6134_, lean_object* v_lo_6135_, lean_object* v_hi_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6133_, v_as_6134_, v_lo_6135_, v_hi_6136_);
lean_dec(v_hi_6136_);
lean_dec(v_n_6133_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6140_, lean_object* v___f_6141_, lean_object* v_filter_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
lean_object* v___y_6151_; lean_object* v___y_6152_; lean_object* v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v_log_6168_; uint8_t v_action_6169_; uint8_t v_wantsRebuild_6170_; lean_object* v_trace_6171_; lean_object* v_buildTime_6172_; lean_object* v___x_6173_; 
v_log_6168_ = lean_ctor_get(v___y_6148_, 0);
v_action_6169_ = lean_ctor_get_uint8(v___y_6148_, sizeof(void*)*3);
v_wantsRebuild_6170_ = lean_ctor_get_uint8(v___y_6148_, sizeof(void*)*3 + 1);
v_trace_6171_ = lean_ctor_get(v___y_6148_, 1);
v_buildTime_6172_ = lean_ctor_get(v___y_6148_, 2);
v___x_6173_ = l_System_FilePath_walkDir(v_path_6140_, v___f_6141_);
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_object* v_a_6174_; lean_object* v___x_6175_; lean_object* v_a_6177_; lean_object* v_a_6178_; lean_object* v___y_6185_; lean_object* v___x_6188_; lean_object* v___x_6189_; uint8_t v___x_6190_; 
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_a_6174_);
lean_dec_ref_known(v___x_6173_, 1);
v___x_6175_ = lean_unsigned_to_nat(0u);
v___x_6188_ = lean_array_get_size(v_a_6174_);
v___x_6189_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6190_ = lean_nat_dec_lt(v___x_6175_, v___x_6188_);
if (v___x_6190_ == 0)
{
lean_dec(v_a_6174_);
lean_dec_ref(v_filter_6142_);
v_a_6177_ = v___x_6189_;
v_a_6178_ = v___y_6148_;
goto v___jp_6176_;
}
else
{
uint8_t v___x_6191_; 
v___x_6191_ = lean_nat_dec_le(v___x_6188_, v___x_6188_);
if (v___x_6191_ == 0)
{
if (v___x_6190_ == 0)
{
lean_dec(v_a_6174_);
lean_dec_ref(v_filter_6142_);
v_a_6177_ = v___x_6189_;
v_a_6178_ = v___y_6148_;
goto v___jp_6176_;
}
else
{
size_t v___x_6192_; size_t v___x_6193_; lean_object* v___x_6194_; 
v___x_6192_ = ((size_t)0ULL);
v___x_6193_ = lean_usize_of_nat(v___x_6188_);
v___x_6194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6142_, v_a_6174_, v___x_6192_, v___x_6193_, v___x_6189_, v___y_6148_);
lean_dec(v_a_6174_);
v___y_6185_ = v___x_6194_;
goto v___jp_6184_;
}
}
else
{
size_t v___x_6195_; size_t v___x_6196_; lean_object* v___x_6197_; 
v___x_6195_ = ((size_t)0ULL);
v___x_6196_ = lean_usize_of_nat(v___x_6188_);
v___x_6197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6142_, v_a_6174_, v___x_6195_, v___x_6196_, v___x_6189_, v___y_6148_);
lean_dec(v_a_6174_);
v___y_6185_ = v___x_6197_;
goto v___jp_6184_;
}
}
v___jp_6176_:
{
lean_object* v___x_6179_; uint8_t v___x_6180_; 
v___x_6179_ = lean_array_get_size(v_a_6177_);
v___x_6180_ = lean_nat_dec_eq(v___x_6179_, v___x_6175_);
if (v___x_6180_ == 0)
{
lean_object* v___x_6181_; lean_object* v___x_6182_; uint8_t v___x_6183_; 
v___x_6181_ = lean_unsigned_to_nat(1u);
v___x_6182_ = lean_nat_sub(v___x_6179_, v___x_6181_);
v___x_6183_ = lean_nat_dec_le(v___x_6175_, v___x_6182_);
if (v___x_6183_ == 0)
{
lean_inc(v___x_6182_);
v___y_6162_ = v___x_6179_;
v___y_6163_ = v_a_6177_;
v___y_6164_ = v_a_6178_;
v___y_6165_ = v___x_6182_;
v___y_6166_ = v___x_6182_;
goto v___jp_6161_;
}
else
{
v___y_6162_ = v___x_6179_;
v___y_6163_ = v_a_6177_;
v___y_6164_ = v_a_6178_;
v___y_6165_ = v___x_6182_;
v___y_6166_ = v___x_6175_;
goto v___jp_6161_;
}
}
else
{
v___y_6151_ = v_a_6178_;
v___y_6152_ = v_a_6177_;
goto v___jp_6150_;
}
}
v___jp_6184_:
{
if (lean_obj_tag(v___y_6185_) == 0)
{
lean_object* v_a_6186_; lean_object* v_a_6187_; 
v_a_6186_ = lean_ctor_get(v___y_6185_, 0);
lean_inc(v_a_6186_);
v_a_6187_ = lean_ctor_get(v___y_6185_, 1);
lean_inc(v_a_6187_);
lean_dec_ref_known(v___y_6185_, 2);
v_a_6177_ = v_a_6186_;
v_a_6178_ = v_a_6187_;
goto v___jp_6176_;
}
else
{
return v___y_6185_;
}
}
}
else
{
lean_object* v___x_6199_; uint8_t v_isShared_6200_; uint8_t v_isSharedCheck_6211_; 
lean_inc(v_buildTime_6172_);
lean_inc_ref(v_trace_6171_);
lean_inc_ref(v_log_6168_);
lean_dec_ref(v_filter_6142_);
v_isSharedCheck_6211_ = !lean_is_exclusive(v___y_6148_);
if (v_isSharedCheck_6211_ == 0)
{
lean_object* v_unused_6212_; lean_object* v_unused_6213_; lean_object* v_unused_6214_; 
v_unused_6212_ = lean_ctor_get(v___y_6148_, 2);
lean_dec(v_unused_6212_);
v_unused_6213_ = lean_ctor_get(v___y_6148_, 1);
lean_dec(v_unused_6213_);
v_unused_6214_ = lean_ctor_get(v___y_6148_, 0);
lean_dec(v_unused_6214_);
v___x_6199_ = v___y_6148_;
v_isShared_6200_ = v_isSharedCheck_6211_;
goto v_resetjp_6198_;
}
else
{
lean_dec(v___y_6148_);
v___x_6199_ = lean_box(0);
v_isShared_6200_ = v_isSharedCheck_6211_;
goto v_resetjp_6198_;
}
v_resetjp_6198_:
{
lean_object* v_a_6201_; lean_object* v___x_6202_; uint8_t v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6208_; 
v_a_6201_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_a_6201_);
lean_dec_ref_known(v___x_6173_, 1);
v___x_6202_ = lean_io_error_to_string(v_a_6201_);
v___x_6203_ = 3;
v___x_6204_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6204_, 0, v___x_6202_);
lean_ctor_set_uint8(v___x_6204_, sizeof(void*)*1, v___x_6203_);
v___x_6205_ = lean_array_get_size(v_log_6168_);
v___x_6206_ = lean_array_push(v_log_6168_, v___x_6204_);
if (v_isShared_6200_ == 0)
{
lean_ctor_set(v___x_6199_, 0, v___x_6206_);
v___x_6208_ = v___x_6199_;
goto v_reusejp_6207_;
}
else
{
lean_object* v_reuseFailAlloc_6210_; 
v_reuseFailAlloc_6210_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6210_, 0, v___x_6206_);
lean_ctor_set(v_reuseFailAlloc_6210_, 1, v_trace_6171_);
lean_ctor_set(v_reuseFailAlloc_6210_, 2, v_buildTime_6172_);
lean_ctor_set_uint8(v_reuseFailAlloc_6210_, sizeof(void*)*3, v_action_6169_);
lean_ctor_set_uint8(v_reuseFailAlloc_6210_, sizeof(void*)*3 + 1, v_wantsRebuild_6170_);
v___x_6208_ = v_reuseFailAlloc_6210_;
goto v_reusejp_6207_;
}
v_reusejp_6207_:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6205_);
lean_ctor_set(v___x_6209_, 1, v___x_6208_);
return v___x_6209_;
}
}
}
v___jp_6150_:
{
lean_object* v___x_6153_; 
v___x_6153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___y_6152_);
lean_ctor_set(v___x_6153_, 1, v___y_6151_);
return v___x_6153_;
}
v___jp_6154_:
{
lean_object* v___x_6160_; 
v___x_6160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6155_, v___y_6157_, v___y_6156_, v___y_6159_);
lean_dec(v___y_6159_);
lean_dec(v___y_6155_);
v___y_6151_ = v___y_6158_;
v___y_6152_ = v___x_6160_;
goto v___jp_6150_;
}
v___jp_6161_:
{
uint8_t v___x_6167_; 
v___x_6167_ = lean_nat_dec_le(v___y_6166_, v___y_6165_);
if (v___x_6167_ == 0)
{
lean_dec(v___y_6165_);
lean_inc(v___y_6166_);
v___y_6155_ = v___y_6162_;
v___y_6156_ = v___y_6166_;
v___y_6157_ = v___y_6163_;
v___y_6158_ = v___y_6164_;
v___y_6159_ = v___y_6166_;
goto v___jp_6154_;
}
else
{
v___y_6155_ = v___y_6162_;
v___y_6156_ = v___y_6166_;
v___y_6157_ = v___y_6163_;
v___y_6158_ = v___y_6164_;
v___y_6159_ = v___y_6165_;
goto v___jp_6154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6215_, lean_object* v___f_6216_, lean_object* v_filter_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l_Lake_inputDir___lam__1(v_path_6215_, v___f_6216_, v_filter_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec(v___y_6221_);
lean_dec(v___y_6220_);
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6226_, size_t v_sz_6227_, size_t v_i_6228_, lean_object* v_bs_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
uint8_t v___x_6237_; 
v___x_6237_ = lean_usize_dec_lt(v_i_6228_, v_sz_6227_);
if (v___x_6237_ == 0)
{
lean_object* v___x_6238_; 
lean_dec_ref(v___y_6230_);
v___x_6238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6238_, 0, v_bs_6229_);
lean_ctor_set(v___x_6238_, 1, v___y_6235_);
return v___x_6238_;
}
else
{
lean_object* v_v_6239_; lean_object* v___x_6240_; lean_object* v_bs_x27_6241_; lean_object* v___y_6243_; 
v_v_6239_ = lean_array_uget(v_bs_6229_, v_i_6228_);
v___x_6240_ = lean_unsigned_to_nat(0u);
v_bs_x27_6241_ = lean_array_uset(v_bs_6229_, v_i_6228_, v___x_6240_);
if (v_text_6226_ == 0)
{
lean_object* v___x_6248_; 
lean_inc_ref(v___y_6230_);
v___x_6248_ = l_Lake_inputBinFile___redArg(v_v_6239_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
v___y_6243_ = v___x_6248_;
goto v___jp_6242_;
}
else
{
lean_object* v___x_6249_; 
lean_inc_ref(v___y_6230_);
v___x_6249_ = l_Lake_inputTextFile___redArg(v_v_6239_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
v___y_6243_ = v___x_6249_;
goto v___jp_6242_;
}
v___jp_6242_:
{
size_t v___x_6244_; size_t v___x_6245_; lean_object* v___x_6246_; 
v___x_6244_ = ((size_t)1ULL);
v___x_6245_ = lean_usize_add(v_i_6228_, v___x_6244_);
v___x_6246_ = lean_array_uset(v_bs_x27_6241_, v_i_6228_, v___y_6243_);
v_i_6228_ = v___x_6245_;
v_bs_6229_ = v___x_6246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6250_, lean_object* v_sz_6251_, lean_object* v_i_6252_, lean_object* v_bs_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_){
_start:
{
uint8_t v_text_boxed_6261_; size_t v_sz_boxed_6262_; size_t v_i_boxed_6263_; lean_object* v_res_6264_; 
v_text_boxed_6261_ = lean_unbox(v_text_6250_);
v_sz_boxed_6262_ = lean_unbox_usize(v_sz_6251_);
lean_dec(v_sz_6251_);
v_i_boxed_6263_ = lean_unbox_usize(v_i_6252_);
lean_dec(v_i_6252_);
v_res_6264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6261_, v_sz_boxed_6262_, v_i_boxed_6263_, v_bs_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
lean_dec_ref(v___y_6258_);
lean_dec(v___y_6257_);
lean_dec(v___y_6256_);
lean_dec(v___y_6255_);
return v_res_6264_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6265_, lean_object* v_path_6266_, lean_object* v_ps_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
size_t v_sz_6275_; size_t v___x_6276_; lean_object* v___x_6277_; 
v_sz_6275_ = lean_array_size(v_ps_6267_);
v___x_6276_ = ((size_t)0ULL);
v___x_6277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6265_, v_sz_6275_, v___x_6276_, v_ps_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_);
if (lean_obj_tag(v___x_6277_) == 0)
{
lean_object* v_a_6278_; lean_object* v_a_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6287_; 
v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
v_a_6279_ = lean_ctor_get(v___x_6277_, 1);
v_isSharedCheck_6287_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6287_ == 0)
{
v___x_6281_ = v___x_6277_;
v_isShared_6282_ = v_isSharedCheck_6287_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_a_6279_);
lean_inc(v_a_6278_);
lean_dec(v___x_6277_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6287_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6283_; lean_object* v___x_6285_; 
v___x_6283_ = l_Lake_Job_collectArray___redArg(v_a_6278_, v_path_6266_);
lean_dec(v_a_6278_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 0, v___x_6283_);
v___x_6285_ = v___x_6281_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v___x_6283_);
lean_ctor_set(v_reuseFailAlloc_6286_, 1, v_a_6279_);
v___x_6285_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
return v___x_6285_;
}
}
}
else
{
lean_object* v_a_6288_; lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6296_; 
lean_dec_ref(v_path_6266_);
v_a_6288_ = lean_ctor_get(v___x_6277_, 0);
v_a_6289_ = lean_ctor_get(v___x_6277_, 1);
v_isSharedCheck_6296_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6296_ == 0)
{
v___x_6291_ = v___x_6277_;
v_isShared_6292_ = v_isSharedCheck_6296_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_inc(v_a_6288_);
lean_dec(v___x_6277_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6296_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6294_; 
if (v_isShared_6292_ == 0)
{
v___x_6294_ = v___x_6291_;
goto v_reusejp_6293_;
}
else
{
lean_object* v_reuseFailAlloc_6295_; 
v_reuseFailAlloc_6295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6295_, 0, v_a_6288_);
lean_ctor_set(v_reuseFailAlloc_6295_, 1, v_a_6289_);
v___x_6294_ = v_reuseFailAlloc_6295_;
goto v_reusejp_6293_;
}
v_reusejp_6293_:
{
return v___x_6294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6297_, lean_object* v_path_6298_, lean_object* v_ps_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_){
_start:
{
uint8_t v_text_boxed_6307_; lean_object* v_res_6308_; 
v_text_boxed_6307_ = lean_unbox(v_text_6297_);
v_res_6308_ = l_Lake_inputDir___lam__2(v_text_boxed_6307_, v_path_6298_, v_ps_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
lean_dec_ref(v___y_6304_);
lean_dec(v___y_6303_);
lean_dec(v___y_6302_);
lean_dec(v___y_6301_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6310_, uint8_t v_text_6311_, lean_object* v_filter_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_){
_start:
{
lean_object* v___f_6320_; lean_object* v___f_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___f_6327_; uint8_t v___x_6328_; lean_object* v___x_6329_; 
v___f_6320_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6310_);
v___f_6321_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6321_, 0, v_path_6310_);
lean_closure_set(v___f_6321_, 1, v___f_6320_);
lean_closure_set(v___f_6321_, 2, v_filter_6312_);
v___x_6322_ = lean_box(0);
v___x_6323_ = lean_unsigned_to_nat(0u);
v___x_6324_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6313_);
v___x_6325_ = l_Lake_Job_async___redArg(v___x_6322_, v___f_6321_, v___x_6323_, v___x_6324_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_);
v___x_6326_ = lean_box(v_text_6311_);
v___f_6327_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6327_, 0, v___x_6326_);
lean_closure_set(v___f_6327_, 1, v_path_6310_);
v___x_6328_ = 0;
v___x_6329_ = l_Lake_Job_bindM___redArg(v___x_6322_, v___x_6325_, v___f_6327_, v___x_6323_, v___x_6328_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
return v___x_6329_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6330_, lean_object* v_text_6331_, lean_object* v_filter_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_){
_start:
{
uint8_t v_text_boxed_6340_; lean_object* v_res_6341_; 
v_text_boxed_6340_ = lean_unbox(v_text_6331_);
v_res_6341_ = l_Lake_inputDir(v_path_6330_, v_text_boxed_6340_, v_filter_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_);
lean_dec_ref(v_a_6338_);
lean_dec_ref(v_a_6337_);
lean_dec(v_a_6336_);
lean_dec(v_a_6335_);
lean_dec(v_a_6334_);
return v_res_6341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6342_, lean_object* v_as_6343_, lean_object* v_lo_6344_, lean_object* v_hi_6345_, lean_object* v_w_6346_, lean_object* v_hlo_6347_, lean_object* v_hhi_6348_){
_start:
{
lean_object* v___x_6349_; 
v___x_6349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6342_, v_as_6343_, v_lo_6344_, v_hi_6345_);
return v___x_6349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6350_, lean_object* v_as_6351_, lean_object* v_lo_6352_, lean_object* v_hi_6353_, lean_object* v_w_6354_, lean_object* v_hlo_6355_, lean_object* v_hhi_6356_){
_start:
{
lean_object* v_res_6357_; 
v_res_6357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6350_, v_as_6351_, v_lo_6352_, v_hi_6353_, v_w_6354_, v_hlo_6355_, v_hhi_6356_);
lean_dec(v_hi_6353_);
lean_dec(v_n_6350_);
return v_res_6357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6358_, lean_object* v_as_6359_, size_t v_i_6360_, size_t v_stop_6361_, lean_object* v_b_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_){
_start:
{
lean_object* v___x_6370_; 
v___x_6370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6358_, v_as_6359_, v_i_6360_, v_stop_6361_, v_b_6362_, v___y_6368_);
return v___x_6370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6371_, lean_object* v_as_6372_, lean_object* v_i_6373_, lean_object* v_stop_6374_, lean_object* v_b_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
size_t v_i_boxed_6383_; size_t v_stop_boxed_6384_; lean_object* v_res_6385_; 
v_i_boxed_6383_ = lean_unbox_usize(v_i_6373_);
lean_dec(v_i_6373_);
v_stop_boxed_6384_ = lean_unbox_usize(v_stop_6374_);
lean_dec(v_stop_6374_);
v_res_6385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6371_, v_as_6372_, v_i_boxed_6383_, v_stop_boxed_6384_, v_b_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_);
lean_dec_ref(v___y_6380_);
lean_dec(v___y_6379_);
lean_dec(v___y_6378_);
lean_dec(v___y_6377_);
lean_dec_ref(v___y_6376_);
lean_dec_ref(v_as_6372_);
return v_res_6385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6386_, lean_object* v_lo_6387_, lean_object* v_hi_6388_, lean_object* v_hhi_6389_, lean_object* v_pivot_6390_, lean_object* v_as_6391_, lean_object* v_i_6392_, lean_object* v_k_6393_, lean_object* v_ilo_6394_, lean_object* v_ik_6395_, lean_object* v_w_6396_){
_start:
{
lean_object* v___x_6397_; 
v___x_6397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6388_, v_pivot_6390_, v_as_6391_, v_i_6392_, v_k_6393_);
return v___x_6397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6398_, lean_object* v_lo_6399_, lean_object* v_hi_6400_, lean_object* v_hhi_6401_, lean_object* v_pivot_6402_, lean_object* v_as_6403_, lean_object* v_i_6404_, lean_object* v_k_6405_, lean_object* v_ilo_6406_, lean_object* v_ik_6407_, lean_object* v_w_6408_){
_start:
{
lean_object* v_res_6409_; 
v_res_6409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6398_, v_lo_6399_, v_hi_6400_, v_hhi_6401_, v_pivot_6402_, v_as_6403_, v_i_6404_, v_k_6405_, v_ilo_6406_, v_ik_6407_, v_w_6408_);
lean_dec_ref(v_pivot_6402_);
lean_dec(v_hi_6400_);
lean_dec(v_lo_6399_);
lean_dec(v_n_6398_);
return v_res_6409_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6410_, lean_object* v_t_6411_){
_start:
{
uint64_t v___x_6412_; uint64_t v___x_6413_; uint64_t v___x_6414_; uint64_t v___x_6415_; 
v___x_6412_ = l_Lake_Hash_nil;
v___x_6413_ = lean_string_hash(v_t_6411_);
v___x_6414_ = lean_uint64_mix_hash(v___x_6412_, v___x_6413_);
v___x_6415_ = lean_uint64_mix_hash(v_ts_6410_, v___x_6414_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6416_, lean_object* v_t_6417_){
_start:
{
uint64_t v_ts_boxed_6418_; uint64_t v_res_6419_; lean_object* v_r_6420_; 
v_ts_boxed_6418_ = lean_unbox_uint64(v_ts_6416_);
lean_dec_ref(v_ts_6416_);
v_res_6419_ = l_Lake_buildO___lam__0(v_ts_boxed_6418_, v_t_6417_);
lean_dec_ref(v_t_6417_);
v_r_6420_ = lean_box_uint64(v_res_6419_);
return v_r_6420_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6421_, lean_object* v_srcFile_6422_, lean_object* v___x_6423_, lean_object* v_compiler_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_){
_start:
{
lean_object* v_log_6432_; uint8_t v_action_6433_; uint8_t v_wantsRebuild_6434_; lean_object* v_trace_6435_; lean_object* v_buildTime_6436_; lean_object* v___x_6438_; uint8_t v_isShared_6439_; uint8_t v_isSharedCheck_6465_; 
v_log_6432_ = lean_ctor_get(v___y_6430_, 0);
v_action_6433_ = lean_ctor_get_uint8(v___y_6430_, sizeof(void*)*3);
v_wantsRebuild_6434_ = lean_ctor_get_uint8(v___y_6430_, sizeof(void*)*3 + 1);
v_trace_6435_ = lean_ctor_get(v___y_6430_, 1);
v_buildTime_6436_ = lean_ctor_get(v___y_6430_, 2);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___y_6430_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6438_ = v___y_6430_;
v_isShared_6439_ = v_isSharedCheck_6465_;
goto v_resetjp_6437_;
}
else
{
lean_inc(v_buildTime_6436_);
lean_inc(v_trace_6435_);
lean_inc(v_log_6432_);
lean_dec(v___y_6430_);
v___x_6438_ = lean_box(0);
v_isShared_6439_ = v_isSharedCheck_6465_;
goto v_resetjp_6437_;
}
v_resetjp_6437_:
{
lean_object* v___x_6440_; 
v___x_6440_ = l_Lake_compileO(v_oFile_6421_, v_srcFile_6422_, v___x_6423_, v_compiler_6424_, v_log_6432_);
if (lean_obj_tag(v___x_6440_) == 0)
{
lean_object* v_a_6441_; lean_object* v_a_6442_; lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6452_; 
v_a_6441_ = lean_ctor_get(v___x_6440_, 0);
v_a_6442_ = lean_ctor_get(v___x_6440_, 1);
v_isSharedCheck_6452_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6452_ == 0)
{
v___x_6444_ = v___x_6440_;
v_isShared_6445_ = v_isSharedCheck_6452_;
goto v_resetjp_6443_;
}
else
{
lean_inc(v_a_6442_);
lean_inc(v_a_6441_);
lean_dec(v___x_6440_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6452_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___x_6447_; 
if (v_isShared_6439_ == 0)
{
lean_ctor_set(v___x_6438_, 0, v_a_6442_);
v___x_6447_ = v___x_6438_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6451_; 
v_reuseFailAlloc_6451_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_a_6442_);
lean_ctor_set(v_reuseFailAlloc_6451_, 1, v_trace_6435_);
lean_ctor_set(v_reuseFailAlloc_6451_, 2, v_buildTime_6436_);
lean_ctor_set_uint8(v_reuseFailAlloc_6451_, sizeof(void*)*3, v_action_6433_);
lean_ctor_set_uint8(v_reuseFailAlloc_6451_, sizeof(void*)*3 + 1, v_wantsRebuild_6434_);
v___x_6447_ = v_reuseFailAlloc_6451_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
lean_object* v___x_6449_; 
if (v_isShared_6445_ == 0)
{
lean_ctor_set(v___x_6444_, 1, v___x_6447_);
v___x_6449_ = v___x_6444_;
goto v_reusejp_6448_;
}
else
{
lean_object* v_reuseFailAlloc_6450_; 
v_reuseFailAlloc_6450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6450_, 0, v_a_6441_);
lean_ctor_set(v_reuseFailAlloc_6450_, 1, v___x_6447_);
v___x_6449_ = v_reuseFailAlloc_6450_;
goto v_reusejp_6448_;
}
v_reusejp_6448_:
{
return v___x_6449_;
}
}
}
}
else
{
lean_object* v_a_6453_; lean_object* v_a_6454_; lean_object* v___x_6456_; uint8_t v_isShared_6457_; uint8_t v_isSharedCheck_6464_; 
v_a_6453_ = lean_ctor_get(v___x_6440_, 0);
v_a_6454_ = lean_ctor_get(v___x_6440_, 1);
v_isSharedCheck_6464_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6464_ == 0)
{
v___x_6456_ = v___x_6440_;
v_isShared_6457_ = v_isSharedCheck_6464_;
goto v_resetjp_6455_;
}
else
{
lean_inc(v_a_6454_);
lean_inc(v_a_6453_);
lean_dec(v___x_6440_);
v___x_6456_ = lean_box(0);
v_isShared_6457_ = v_isSharedCheck_6464_;
goto v_resetjp_6455_;
}
v_resetjp_6455_:
{
lean_object* v___x_6459_; 
if (v_isShared_6439_ == 0)
{
lean_ctor_set(v___x_6438_, 0, v_a_6454_);
v___x_6459_ = v___x_6438_;
goto v_reusejp_6458_;
}
else
{
lean_object* v_reuseFailAlloc_6463_; 
v_reuseFailAlloc_6463_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6463_, 0, v_a_6454_);
lean_ctor_set(v_reuseFailAlloc_6463_, 1, v_trace_6435_);
lean_ctor_set(v_reuseFailAlloc_6463_, 2, v_buildTime_6436_);
lean_ctor_set_uint8(v_reuseFailAlloc_6463_, sizeof(void*)*3, v_action_6433_);
lean_ctor_set_uint8(v_reuseFailAlloc_6463_, sizeof(void*)*3 + 1, v_wantsRebuild_6434_);
v___x_6459_ = v_reuseFailAlloc_6463_;
goto v_reusejp_6458_;
}
v_reusejp_6458_:
{
lean_object* v___x_6461_; 
if (v_isShared_6457_ == 0)
{
lean_ctor_set(v___x_6456_, 1, v___x_6459_);
v___x_6461_ = v___x_6456_;
goto v_reusejp_6460_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v_a_6453_);
lean_ctor_set(v_reuseFailAlloc_6462_, 1, v___x_6459_);
v___x_6461_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6460_;
}
v_reusejp_6460_:
{
return v___x_6461_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6466_, lean_object* v_srcFile_6467_, lean_object* v___x_6468_, lean_object* v_compiler_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_){
_start:
{
lean_object* v_res_6477_; 
v_res_6477_ = l_Lake_buildO___lam__1(v_oFile_6466_, v_srcFile_6467_, v___x_6468_, v_compiler_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_);
lean_dec_ref(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec(v___y_6471_);
lean_dec_ref(v___y_6470_);
lean_dec_ref(v___x_6468_);
return v_res_6477_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6481_; lean_object* v___x_6482_; 
v___x_6481_ = l_Lake_Hash_nil;
v___x_6482_ = lean_box_uint64(v___x_6481_);
return v___x_6482_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6483_, lean_object* v___f_6484_, lean_object* v_extraDepTrace_6485_, lean_object* v_weakArgs_6486_, lean_object* v_oFile_6487_, lean_object* v_compiler_6488_, lean_object* v___x_6489_, lean_object* v___f_6490_, lean_object* v_srcFile_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_){
_start:
{
lean_object* v_log_6499_; uint8_t v_action_6500_; uint8_t v_wantsRebuild_6501_; lean_object* v_trace_6502_; lean_object* v_buildTime_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6588_; 
v_log_6499_ = lean_ctor_get(v___y_6497_, 0);
v_action_6500_ = lean_ctor_get_uint8(v___y_6497_, sizeof(void*)*3);
v_wantsRebuild_6501_ = lean_ctor_get_uint8(v___y_6497_, sizeof(void*)*3 + 1);
v_trace_6502_ = lean_ctor_get(v___y_6497_, 1);
v_buildTime_6503_ = lean_ctor_get(v___y_6497_, 2);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___y_6497_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6505_ = v___y_6497_;
v_isShared_6506_ = v_isSharedCheck_6588_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_buildTime_6503_);
lean_inc(v_trace_6502_);
lean_inc(v_log_6499_);
lean_dec(v___y_6497_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6588_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v___x_6507_; lean_object* v___x_6508_; uint64_t v___y_6510_; uint64_t v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; uint8_t v___x_6576_; 
v___x_6507_ = l_Lake_platformTrace;
v___x_6508_ = l_Lake_BuildTrace_mix(v_trace_6502_, v___x_6507_);
v___x_6573_ = l_Lake_Hash_nil;
v___x_6574_ = lean_unsigned_to_nat(0u);
v___x_6575_ = lean_array_get_size(v_traceArgs_6483_);
v___x_6576_ = lean_nat_dec_lt(v___x_6574_, v___x_6575_);
if (v___x_6576_ == 0)
{
lean_dec_ref(v___f_6490_);
lean_dec_ref(v___x_6489_);
v___y_6510_ = v___x_6573_;
goto v___jp_6509_;
}
else
{
uint8_t v___x_6577_; 
v___x_6577_ = lean_nat_dec_le(v___x_6575_, v___x_6575_);
if (v___x_6577_ == 0)
{
if (v___x_6576_ == 0)
{
lean_dec_ref(v___f_6490_);
lean_dec_ref(v___x_6489_);
v___y_6510_ = v___x_6573_;
goto v___jp_6509_;
}
else
{
size_t v___x_6578_; size_t v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; uint64_t v___x_6582_; 
v___x_6578_ = ((size_t)0ULL);
v___x_6579_ = lean_usize_of_nat(v___x_6575_);
v___x_6580_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6483_);
v___x_6581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6489_, v___f_6490_, v_traceArgs_6483_, v___x_6578_, v___x_6579_, v___x_6580_);
v___x_6582_ = lean_unbox_uint64(v___x_6581_);
lean_dec(v___x_6581_);
v___y_6510_ = v___x_6582_;
goto v___jp_6509_;
}
}
else
{
size_t v___x_6583_; size_t v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; uint64_t v___x_6587_; 
v___x_6583_ = ((size_t)0ULL);
v___x_6584_ = lean_usize_of_nat(v___x_6575_);
v___x_6585_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6483_);
v___x_6586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6489_, v___f_6490_, v_traceArgs_6483_, v___x_6583_, v___x_6584_, v___x_6585_);
v___x_6587_ = lean_unbox_uint64(v___x_6586_);
lean_dec(v___x_6586_);
v___y_6510_ = v___x_6587_;
goto v___jp_6509_;
}
}
v___jp_6509_:
{
lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6522_; 
v___x_6511_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6512_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6483_);
v___x_6513_ = lean_array_to_list(v_traceArgs_6483_);
v___x_6514_ = l_List_toString___redArg(v___f_6484_, v___x_6513_);
v___x_6515_ = lean_string_append(v___x_6512_, v___x_6514_);
lean_dec_ref(v___x_6514_);
v___x_6516_ = lean_string_append(v___x_6511_, v___x_6515_);
lean_dec_ref(v___x_6515_);
v___x_6517_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6518_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6519_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6519_, 0, v___x_6516_);
lean_ctor_set(v___x_6519_, 1, v___x_6517_);
lean_ctor_set(v___x_6519_, 2, v___x_6518_);
lean_ctor_set_uint64(v___x_6519_, sizeof(void*)*3, v___y_6510_);
v___x_6520_ = l_Lake_BuildTrace_mix(v___x_6508_, v___x_6519_);
if (v_isShared_6506_ == 0)
{
lean_ctor_set(v___x_6505_, 1, v___x_6520_);
v___x_6522_ = v___x_6505_;
goto v_reusejp_6521_;
}
else
{
lean_object* v_reuseFailAlloc_6572_; 
v_reuseFailAlloc_6572_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_log_6499_);
lean_ctor_set(v_reuseFailAlloc_6572_, 1, v___x_6520_);
lean_ctor_set(v_reuseFailAlloc_6572_, 2, v_buildTime_6503_);
lean_ctor_set_uint8(v_reuseFailAlloc_6572_, sizeof(void*)*3, v_action_6500_);
lean_ctor_set_uint8(v_reuseFailAlloc_6572_, sizeof(void*)*3 + 1, v_wantsRebuild_6501_);
v___x_6522_ = v_reuseFailAlloc_6572_;
goto v_reusejp_6521_;
}
v_reusejp_6521_:
{
lean_object* v___x_6523_; 
lean_inc_ref(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc_ref(v___y_6492_);
v___x_6523_ = lean_apply_7(v_extraDepTrace_6485_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___x_6522_, lean_box(0));
if (lean_obj_tag(v___x_6523_) == 0)
{
lean_object* v_a_6524_; lean_object* v_a_6525_; lean_object* v_log_6526_; uint8_t v_action_6527_; uint8_t v_wantsRebuild_6528_; lean_object* v_trace_6529_; lean_object* v_buildTime_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6562_; 
v_a_6524_ = lean_ctor_get(v___x_6523_, 1);
lean_inc(v_a_6524_);
v_a_6525_ = lean_ctor_get(v___x_6523_, 0);
lean_inc(v_a_6525_);
lean_dec_ref_known(v___x_6523_, 2);
v_log_6526_ = lean_ctor_get(v_a_6524_, 0);
v_action_6527_ = lean_ctor_get_uint8(v_a_6524_, sizeof(void*)*3);
v_wantsRebuild_6528_ = lean_ctor_get_uint8(v_a_6524_, sizeof(void*)*3 + 1);
v_trace_6529_ = lean_ctor_get(v_a_6524_, 1);
v_buildTime_6530_ = lean_ctor_get(v_a_6524_, 2);
v_isSharedCheck_6562_ = !lean_is_exclusive(v_a_6524_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6532_ = v_a_6524_;
v_isShared_6533_ = v_isSharedCheck_6562_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_buildTime_6530_);
lean_inc(v_trace_6529_);
lean_inc(v_log_6526_);
lean_dec(v_a_6524_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6562_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6534_; lean_object* v___x_6536_; 
v___x_6534_ = l_Lake_BuildTrace_mix(v_trace_6529_, v_a_6525_);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 1, v___x_6534_);
v___x_6536_ = v___x_6532_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_log_6526_);
lean_ctor_set(v_reuseFailAlloc_6561_, 1, v___x_6534_);
lean_ctor_set(v_reuseFailAlloc_6561_, 2, v_buildTime_6530_);
lean_ctor_set_uint8(v_reuseFailAlloc_6561_, sizeof(void*)*3, v_action_6527_);
lean_ctor_set_uint8(v_reuseFailAlloc_6561_, sizeof(void*)*3 + 1, v_wantsRebuild_6528_);
v___x_6536_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
lean_object* v___x_6537_; lean_object* v___f_6538_; uint8_t v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; 
v___x_6537_ = l_Array_append___redArg(v_weakArgs_6486_, v_traceArgs_6483_);
lean_dec_ref(v_traceArgs_6483_);
lean_inc_ref(v_oFile_6487_);
v___f_6538_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6538_, 0, v_oFile_6487_);
lean_closure_set(v___f_6538_, 1, v_srcFile_6491_);
lean_closure_set(v___f_6538_, 2, v___x_6537_);
lean_closure_set(v___f_6538_, 3, v_compiler_6488_);
v___x_6539_ = 0;
v___x_6540_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6541_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6487_, v___f_6538_, v___x_6539_, v___x_6540_, v___x_6539_, v___x_6539_, v___x_6539_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___x_6536_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_a_6542_; lean_object* v_a_6543_; lean_object* v___x_6545_; uint8_t v_isShared_6546_; uint8_t v_isSharedCheck_6551_; 
v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
v_a_6543_ = lean_ctor_get(v___x_6541_, 1);
v_isSharedCheck_6551_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6551_ == 0)
{
v___x_6545_ = v___x_6541_;
v_isShared_6546_ = v_isSharedCheck_6551_;
goto v_resetjp_6544_;
}
else
{
lean_inc(v_a_6543_);
lean_inc(v_a_6542_);
lean_dec(v___x_6541_);
v___x_6545_ = lean_box(0);
v_isShared_6546_ = v_isSharedCheck_6551_;
goto v_resetjp_6544_;
}
v_resetjp_6544_:
{
lean_object* v_path_6547_; lean_object* v___x_6549_; 
v_path_6547_ = lean_ctor_get(v_a_6542_, 1);
lean_inc_ref(v_path_6547_);
lean_dec(v_a_6542_);
if (v_isShared_6546_ == 0)
{
lean_ctor_set(v___x_6545_, 0, v_path_6547_);
v___x_6549_ = v___x_6545_;
goto v_reusejp_6548_;
}
else
{
lean_object* v_reuseFailAlloc_6550_; 
v_reuseFailAlloc_6550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_path_6547_);
lean_ctor_set(v_reuseFailAlloc_6550_, 1, v_a_6543_);
v___x_6549_ = v_reuseFailAlloc_6550_;
goto v_reusejp_6548_;
}
v_reusejp_6548_:
{
return v___x_6549_;
}
}
}
else
{
lean_object* v_a_6552_; lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
v_a_6552_ = lean_ctor_get(v___x_6541_, 0);
v_a_6553_ = lean_ctor_get(v___x_6541_, 1);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6541_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_inc(v_a_6552_);
lean_dec(v___x_6541_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6552_);
lean_ctor_set(v_reuseFailAlloc_6559_, 1, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
}
}
else
{
lean_object* v_a_6563_; lean_object* v_a_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6571_; 
lean_dec_ref(v___y_6492_);
lean_dec_ref(v_srcFile_6491_);
lean_dec_ref(v_compiler_6488_);
lean_dec_ref(v_oFile_6487_);
lean_dec_ref(v_weakArgs_6486_);
lean_dec_ref(v_traceArgs_6483_);
v_a_6563_ = lean_ctor_get(v___x_6523_, 0);
v_a_6564_ = lean_ctor_get(v___x_6523_, 1);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6523_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6566_ = v___x_6523_;
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_a_6564_);
lean_inc(v_a_6563_);
lean_dec(v___x_6523_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v___x_6569_; 
if (v_isShared_6567_ == 0)
{
v___x_6569_ = v___x_6566_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6563_);
lean_ctor_set(v_reuseFailAlloc_6570_, 1, v_a_6564_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
return v___x_6569_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6589_, lean_object* v___f_6590_, lean_object* v_extraDepTrace_6591_, lean_object* v_weakArgs_6592_, lean_object* v_oFile_6593_, lean_object* v_compiler_6594_, lean_object* v___x_6595_, lean_object* v___f_6596_, lean_object* v_srcFile_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_){
_start:
{
lean_object* v_res_6605_; 
v_res_6605_ = l_Lake_buildO___lam__2(v_traceArgs_6589_, v___f_6590_, v_extraDepTrace_6591_, v_weakArgs_6592_, v_oFile_6593_, v_compiler_6594_, v___x_6595_, v___f_6596_, v_srcFile_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_);
lean_dec_ref(v___y_6602_);
lean_dec(v___y_6601_);
lean_dec(v___y_6600_);
lean_dec(v___y_6599_);
return v_res_6605_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6608_, lean_object* v_srcJob_6609_, lean_object* v_weakArgs_6610_, lean_object* v_traceArgs_6611_, lean_object* v_compiler_6612_, lean_object* v_extraDepTrace_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_){
_start:
{
lean_object* v___f_6621_; lean_object* v___x_6622_; lean_object* v___f_6623_; lean_object* v___x_6624_; lean_object* v___f_6625_; lean_object* v___x_6626_; uint8_t v___x_6627_; lean_object* v___x_6628_; 
v___f_6621_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6622_ = l_Lake_instDataKindFilePath;
v___f_6623_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6624_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6625_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6625_, 0, v_traceArgs_6611_);
lean_closure_set(v___f_6625_, 1, v___f_6623_);
lean_closure_set(v___f_6625_, 2, v_extraDepTrace_6613_);
lean_closure_set(v___f_6625_, 3, v_weakArgs_6610_);
lean_closure_set(v___f_6625_, 4, v_oFile_6608_);
lean_closure_set(v___f_6625_, 5, v_compiler_6612_);
lean_closure_set(v___f_6625_, 6, v___x_6624_);
lean_closure_set(v___f_6625_, 7, v___f_6621_);
v___x_6626_ = lean_unsigned_to_nat(0u);
v___x_6627_ = 0;
v___x_6628_ = l_Lake_Job_mapM___redArg(v___x_6622_, v_srcJob_6609_, v___f_6625_, v___x_6626_, v___x_6627_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_);
return v___x_6628_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6629_, lean_object* v_srcJob_6630_, lean_object* v_weakArgs_6631_, lean_object* v_traceArgs_6632_, lean_object* v_compiler_6633_, lean_object* v_extraDepTrace_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l_Lake_buildO(v_oFile_6629_, v_srcJob_6630_, v_weakArgs_6631_, v_traceArgs_6632_, v_compiler_6633_, v_extraDepTrace_6634_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_);
lean_dec_ref(v_a_6640_);
lean_dec_ref(v_a_6639_);
lean_dec(v_a_6638_);
lean_dec(v_a_6637_);
lean_dec(v_a_6636_);
return v_res_6642_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
v___x_6644_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6645_ = lean_unsigned_to_nat(2u);
v___x_6646_ = lean_mk_empty_array_with_capacity(v___x_6645_);
v___x_6647_ = lean_array_push(v___x_6646_, v___x_6644_);
return v___x_6647_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6648_, lean_object* v_traceArgs_6649_, lean_object* v_oFile_6650_, lean_object* v_srcFile_6651_, lean_object* v_leanIncludeDir_x3f_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_){
_start:
{
lean_object* v_toContext_6660_; lean_object* v_lakeEnv_6661_; lean_object* v_log_6662_; uint8_t v_action_6663_; uint8_t v_wantsRebuild_6664_; lean_object* v_trace_6665_; lean_object* v_buildTime_6666_; lean_object* v___x_6668_; uint8_t v_isShared_6669_; uint8_t v_isSharedCheck_6707_; 
v_toContext_6660_ = lean_ctor_get(v___y_6657_, 1);
v_lakeEnv_6661_ = lean_ctor_get(v_toContext_6660_, 0);
v_log_6662_ = lean_ctor_get(v___y_6658_, 0);
v_action_6663_ = lean_ctor_get_uint8(v___y_6658_, sizeof(void*)*3);
v_wantsRebuild_6664_ = lean_ctor_get_uint8(v___y_6658_, sizeof(void*)*3 + 1);
v_trace_6665_ = lean_ctor_get(v___y_6658_, 1);
v_buildTime_6666_ = lean_ctor_get(v___y_6658_, 2);
v_isSharedCheck_6707_ = !lean_is_exclusive(v___y_6658_);
if (v_isSharedCheck_6707_ == 0)
{
v___x_6668_ = v___y_6658_;
v_isShared_6669_ = v_isSharedCheck_6707_;
goto v_resetjp_6667_;
}
else
{
lean_inc(v_buildTime_6666_);
lean_inc(v_trace_6665_);
lean_inc(v_log_6662_);
lean_dec(v___y_6658_);
v___x_6668_ = lean_box(0);
v_isShared_6669_ = v_isSharedCheck_6707_;
goto v_resetjp_6667_;
}
v_resetjp_6667_:
{
lean_object* v_lean_6670_; lean_object* v___y_6672_; 
v_lean_6670_ = lean_ctor_get(v_lakeEnv_6661_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6652_) == 0)
{
lean_object* v_includeDir_6705_; 
v_includeDir_6705_ = lean_ctor_get(v_lean_6670_, 4);
lean_inc_ref(v_includeDir_6705_);
v___y_6672_ = v_includeDir_6705_;
goto v___jp_6671_;
}
else
{
lean_object* v_val_6706_; 
v_val_6706_ = lean_ctor_get(v_leanIncludeDir_x3f_6652_, 0);
lean_inc(v_val_6706_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6652_, 1);
v___y_6672_ = v_val_6706_;
goto v___jp_6671_;
}
v___jp_6671_:
{
lean_object* v_cc_6673_; lean_object* v_ccFlags_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; 
v_cc_6673_ = lean_ctor_get(v_lean_6670_, 14);
v_ccFlags_6674_ = lean_ctor_get(v_lean_6670_, 18);
v___x_6675_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6676_ = lean_array_push(v___x_6675_, v___y_6672_);
v___x_6677_ = l_Array_append___redArg(v___x_6676_, v_ccFlags_6674_);
v___x_6678_ = l_Array_append___redArg(v___x_6677_, v_weakArgs_6648_);
v___x_6679_ = l_Array_append___redArg(v___x_6678_, v_traceArgs_6649_);
lean_inc_ref(v_cc_6673_);
v___x_6680_ = l_Lake_compileO(v_oFile_6650_, v_srcFile_6651_, v___x_6679_, v_cc_6673_, v_log_6662_);
lean_dec_ref(v___x_6679_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; lean_object* v_a_6682_; lean_object* v___x_6684_; uint8_t v_isShared_6685_; uint8_t v_isSharedCheck_6692_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
v_a_6682_ = lean_ctor_get(v___x_6680_, 1);
v_isSharedCheck_6692_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6692_ == 0)
{
v___x_6684_ = v___x_6680_;
v_isShared_6685_ = v_isSharedCheck_6692_;
goto v_resetjp_6683_;
}
else
{
lean_inc(v_a_6682_);
lean_inc(v_a_6681_);
lean_dec(v___x_6680_);
v___x_6684_ = lean_box(0);
v_isShared_6685_ = v_isSharedCheck_6692_;
goto v_resetjp_6683_;
}
v_resetjp_6683_:
{
lean_object* v___x_6687_; 
if (v_isShared_6669_ == 0)
{
lean_ctor_set(v___x_6668_, 0, v_a_6682_);
v___x_6687_ = v___x_6668_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6691_; 
v_reuseFailAlloc_6691_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6691_, 0, v_a_6682_);
lean_ctor_set(v_reuseFailAlloc_6691_, 1, v_trace_6665_);
lean_ctor_set(v_reuseFailAlloc_6691_, 2, v_buildTime_6666_);
lean_ctor_set_uint8(v_reuseFailAlloc_6691_, sizeof(void*)*3, v_action_6663_);
lean_ctor_set_uint8(v_reuseFailAlloc_6691_, sizeof(void*)*3 + 1, v_wantsRebuild_6664_);
v___x_6687_ = v_reuseFailAlloc_6691_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
lean_object* v___x_6689_; 
if (v_isShared_6685_ == 0)
{
lean_ctor_set(v___x_6684_, 1, v___x_6687_);
v___x_6689_ = v___x_6684_;
goto v_reusejp_6688_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v_a_6681_);
lean_ctor_set(v_reuseFailAlloc_6690_, 1, v___x_6687_);
v___x_6689_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6688_;
}
v_reusejp_6688_:
{
return v___x_6689_;
}
}
}
}
else
{
lean_object* v_a_6693_; lean_object* v_a_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6704_; 
v_a_6693_ = lean_ctor_get(v___x_6680_, 0);
v_a_6694_ = lean_ctor_get(v___x_6680_, 1);
v_isSharedCheck_6704_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6704_ == 0)
{
v___x_6696_ = v___x_6680_;
v_isShared_6697_ = v_isSharedCheck_6704_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_a_6694_);
lean_inc(v_a_6693_);
lean_dec(v___x_6680_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6704_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v___x_6699_; 
if (v_isShared_6669_ == 0)
{
lean_ctor_set(v___x_6668_, 0, v_a_6694_);
v___x_6699_ = v___x_6668_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6703_; 
v_reuseFailAlloc_6703_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6703_, 0, v_a_6694_);
lean_ctor_set(v_reuseFailAlloc_6703_, 1, v_trace_6665_);
lean_ctor_set(v_reuseFailAlloc_6703_, 2, v_buildTime_6666_);
lean_ctor_set_uint8(v_reuseFailAlloc_6703_, sizeof(void*)*3, v_action_6663_);
lean_ctor_set_uint8(v_reuseFailAlloc_6703_, sizeof(void*)*3 + 1, v_wantsRebuild_6664_);
v___x_6699_ = v_reuseFailAlloc_6703_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
lean_object* v___x_6701_; 
if (v_isShared_6697_ == 0)
{
lean_ctor_set(v___x_6696_, 1, v___x_6699_);
v___x_6701_ = v___x_6696_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6693_);
lean_ctor_set(v_reuseFailAlloc_6702_, 1, v___x_6699_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6708_, lean_object* v_traceArgs_6709_, lean_object* v_oFile_6710_, lean_object* v_srcFile_6711_, lean_object* v_leanIncludeDir_x3f_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_){
_start:
{
lean_object* v_res_6720_; 
v_res_6720_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6708_, v_traceArgs_6709_, v_oFile_6710_, v_srcFile_6711_, v_leanIncludeDir_x3f_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_);
lean_dec_ref(v___y_6717_);
lean_dec(v___y_6716_);
lean_dec(v___y_6715_);
lean_dec(v___y_6714_);
lean_dec_ref(v___y_6713_);
lean_dec_ref(v_traceArgs_6709_);
lean_dec_ref(v_weakArgs_6708_);
return v_res_6720_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6721_, size_t v_i_6722_, size_t v_stop_6723_, uint64_t v_b_6724_){
_start:
{
uint8_t v___x_6725_; 
v___x_6725_ = lean_usize_dec_eq(v_i_6722_, v_stop_6723_);
if (v___x_6725_ == 0)
{
lean_object* v___x_6726_; uint64_t v___x_6727_; uint64_t v___x_6728_; uint64_t v___x_6729_; uint64_t v___x_6730_; size_t v___x_6731_; size_t v___x_6732_; 
v___x_6726_ = lean_array_uget_borrowed(v_as_6721_, v_i_6722_);
v___x_6727_ = l_Lake_Hash_nil;
v___x_6728_ = lean_string_hash(v___x_6726_);
v___x_6729_ = lean_uint64_mix_hash(v___x_6727_, v___x_6728_);
v___x_6730_ = lean_uint64_mix_hash(v_b_6724_, v___x_6729_);
v___x_6731_ = ((size_t)1ULL);
v___x_6732_ = lean_usize_add(v_i_6722_, v___x_6731_);
v_i_6722_ = v___x_6732_;
v_b_6724_ = v___x_6730_;
goto _start;
}
else
{
return v_b_6724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6734_, lean_object* v_i_6735_, lean_object* v_stop_6736_, lean_object* v_b_6737_){
_start:
{
size_t v_i_boxed_6738_; size_t v_stop_boxed_6739_; uint64_t v_b_boxed_6740_; uint64_t v_res_6741_; lean_object* v_r_6742_; 
v_i_boxed_6738_ = lean_unbox_usize(v_i_6735_);
lean_dec(v_i_6735_);
v_stop_boxed_6739_ = lean_unbox_usize(v_stop_6736_);
lean_dec(v_stop_6736_);
v_b_boxed_6740_ = lean_unbox_uint64(v_b_6737_);
lean_dec_ref(v_b_6737_);
v_res_6741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6734_, v_i_boxed_6738_, v_stop_boxed_6739_, v_b_boxed_6740_);
lean_dec_ref(v_as_6734_);
v_r_6742_ = lean_box_uint64(v_res_6741_);
return v_r_6742_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6744_, lean_object* v_x_6745_){
_start:
{
if (lean_obj_tag(v_x_6745_) == 0)
{
return v_x_6744_;
}
else
{
lean_object* v_head_6746_; lean_object* v_tail_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; 
v_head_6746_ = lean_ctor_get(v_x_6745_, 0);
v_tail_6747_ = lean_ctor_get(v_x_6745_, 1);
v___x_6748_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6749_ = lean_string_append(v_x_6744_, v___x_6748_);
v___x_6750_ = lean_string_append(v___x_6749_, v_head_6746_);
v_x_6744_ = v___x_6750_;
v_x_6745_ = v_tail_6747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6752_, lean_object* v_x_6753_){
_start:
{
lean_object* v_res_6754_; 
v_res_6754_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6752_, v_x_6753_);
lean_dec(v_x_6753_);
return v_res_6754_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6758_){
_start:
{
if (lean_obj_tag(v_x_6758_) == 0)
{
lean_object* v___x_6759_; 
v___x_6759_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6759_;
}
else
{
lean_object* v_tail_6760_; 
v_tail_6760_ = lean_ctor_get(v_x_6758_, 1);
if (lean_obj_tag(v_tail_6760_) == 0)
{
lean_object* v_head_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; 
v_head_6761_ = lean_ctor_get(v_x_6758_, 0);
v___x_6762_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6763_ = lean_string_append(v___x_6762_, v_head_6761_);
v___x_6764_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6765_ = lean_string_append(v___x_6763_, v___x_6764_);
return v___x_6765_;
}
else
{
lean_object* v_head_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; uint32_t v___x_6770_; lean_object* v___x_6771_; 
v_head_6766_ = lean_ctor_get(v_x_6758_, 0);
v___x_6767_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6768_ = lean_string_append(v___x_6767_, v_head_6766_);
v___x_6769_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6768_, v_tail_6760_);
v___x_6770_ = 93;
v___x_6771_ = lean_string_push(v___x_6769_, v___x_6770_);
return v___x_6771_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6772_){
_start:
{
lean_object* v_res_6773_; 
v_res_6773_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6772_);
lean_dec(v_x_6772_);
return v_res_6773_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6774_, lean_object* v_traceArgs_6775_, lean_object* v_oFile_6776_, lean_object* v_leanIncludeDir_x3f_6777_, lean_object* v_srcFile_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_){
_start:
{
lean_object* v_log_6786_; uint8_t v_action_6787_; uint8_t v_wantsRebuild_6788_; lean_object* v_trace_6789_; lean_object* v_buildTime_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6847_; 
v_log_6786_ = lean_ctor_get(v___y_6784_, 0);
v_action_6787_ = lean_ctor_get_uint8(v___y_6784_, sizeof(void*)*3);
v_wantsRebuild_6788_ = lean_ctor_get_uint8(v___y_6784_, sizeof(void*)*3 + 1);
v_trace_6789_ = lean_ctor_get(v___y_6784_, 1);
v_buildTime_6790_ = lean_ctor_get(v___y_6784_, 2);
v_isSharedCheck_6847_ = !lean_is_exclusive(v___y_6784_);
if (v_isSharedCheck_6847_ == 0)
{
v___x_6792_ = v___y_6784_;
v_isShared_6793_ = v_isSharedCheck_6847_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_buildTime_6790_);
lean_inc(v_trace_6789_);
lean_inc(v_log_6786_);
lean_dec(v___y_6784_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6847_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v_leanTrace_6794_; lean_object* v___f_6795_; lean_object* v___x_6796_; uint64_t v___y_6798_; uint64_t v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; uint8_t v___x_6839_; 
v_leanTrace_6794_ = lean_ctor_get(v___y_6783_, 2);
lean_inc_ref(v_oFile_6776_);
lean_inc_ref(v_traceArgs_6775_);
v___f_6795_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6795_, 0, v_weakArgs_6774_);
lean_closure_set(v___f_6795_, 1, v_traceArgs_6775_);
lean_closure_set(v___f_6795_, 2, v_oFile_6776_);
lean_closure_set(v___f_6795_, 3, v_srcFile_6778_);
lean_closure_set(v___f_6795_, 4, v_leanIncludeDir_x3f_6777_);
lean_inc_ref(v_leanTrace_6794_);
v___x_6796_ = l_Lake_BuildTrace_mix(v_trace_6789_, v_leanTrace_6794_);
v___x_6836_ = l_Lake_Hash_nil;
v___x_6837_ = lean_unsigned_to_nat(0u);
v___x_6838_ = lean_array_get_size(v_traceArgs_6775_);
v___x_6839_ = lean_nat_dec_lt(v___x_6837_, v___x_6838_);
if (v___x_6839_ == 0)
{
v___y_6798_ = v___x_6836_;
goto v___jp_6797_;
}
else
{
uint8_t v___x_6840_; 
v___x_6840_ = lean_nat_dec_le(v___x_6838_, v___x_6838_);
if (v___x_6840_ == 0)
{
if (v___x_6839_ == 0)
{
v___y_6798_ = v___x_6836_;
goto v___jp_6797_;
}
else
{
size_t v___x_6841_; size_t v___x_6842_; uint64_t v___x_6843_; 
v___x_6841_ = ((size_t)0ULL);
v___x_6842_ = lean_usize_of_nat(v___x_6838_);
v___x_6843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6775_, v___x_6841_, v___x_6842_, v___x_6836_);
v___y_6798_ = v___x_6843_;
goto v___jp_6797_;
}
}
else
{
size_t v___x_6844_; size_t v___x_6845_; uint64_t v___x_6846_; 
v___x_6844_ = ((size_t)0ULL);
v___x_6845_ = lean_usize_of_nat(v___x_6838_);
v___x_6846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6775_, v___x_6844_, v___x_6845_, v___x_6836_);
v___y_6798_ = v___x_6846_;
goto v___jp_6797_;
}
}
v___jp_6797_:
{
lean_object* v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6812_; 
v___x_6799_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6800_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6801_ = lean_array_to_list(v_traceArgs_6775_);
v___x_6802_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6801_);
lean_dec(v___x_6801_);
v___x_6803_ = lean_string_append(v___x_6800_, v___x_6802_);
lean_dec_ref(v___x_6802_);
v___x_6804_ = lean_string_append(v___x_6799_, v___x_6803_);
lean_dec_ref(v___x_6803_);
v___x_6805_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6806_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6807_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6807_, 0, v___x_6804_);
lean_ctor_set(v___x_6807_, 1, v___x_6805_);
lean_ctor_set(v___x_6807_, 2, v___x_6806_);
lean_ctor_set_uint64(v___x_6807_, sizeof(void*)*3, v___y_6798_);
v___x_6808_ = l_Lake_BuildTrace_mix(v___x_6796_, v___x_6807_);
v___x_6809_ = l_Lake_platformTrace;
v___x_6810_ = l_Lake_BuildTrace_mix(v___x_6808_, v___x_6809_);
if (v_isShared_6793_ == 0)
{
lean_ctor_set(v___x_6792_, 1, v___x_6810_);
v___x_6812_ = v___x_6792_;
goto v_reusejp_6811_;
}
else
{
lean_object* v_reuseFailAlloc_6835_; 
v_reuseFailAlloc_6835_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6835_, 0, v_log_6786_);
lean_ctor_set(v_reuseFailAlloc_6835_, 1, v___x_6810_);
lean_ctor_set(v_reuseFailAlloc_6835_, 2, v_buildTime_6790_);
lean_ctor_set_uint8(v_reuseFailAlloc_6835_, sizeof(void*)*3, v_action_6787_);
lean_ctor_set_uint8(v_reuseFailAlloc_6835_, sizeof(void*)*3 + 1, v_wantsRebuild_6788_);
v___x_6812_ = v_reuseFailAlloc_6835_;
goto v_reusejp_6811_;
}
v_reusejp_6811_:
{
uint8_t v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; 
v___x_6813_ = 0;
v___x_6814_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6815_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6776_, v___f_6795_, v___x_6813_, v___x_6814_, v___x_6813_, v___x_6813_, v___x_6813_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___x_6812_);
if (lean_obj_tag(v___x_6815_) == 0)
{
lean_object* v_a_6816_; lean_object* v_a_6817_; lean_object* v___x_6819_; uint8_t v_isShared_6820_; uint8_t v_isSharedCheck_6825_; 
v_a_6816_ = lean_ctor_get(v___x_6815_, 0);
v_a_6817_ = lean_ctor_get(v___x_6815_, 1);
v_isSharedCheck_6825_ = !lean_is_exclusive(v___x_6815_);
if (v_isSharedCheck_6825_ == 0)
{
v___x_6819_ = v___x_6815_;
v_isShared_6820_ = v_isSharedCheck_6825_;
goto v_resetjp_6818_;
}
else
{
lean_inc(v_a_6817_);
lean_inc(v_a_6816_);
lean_dec(v___x_6815_);
v___x_6819_ = lean_box(0);
v_isShared_6820_ = v_isSharedCheck_6825_;
goto v_resetjp_6818_;
}
v_resetjp_6818_:
{
lean_object* v_path_6821_; lean_object* v___x_6823_; 
v_path_6821_ = lean_ctor_get(v_a_6816_, 1);
lean_inc_ref(v_path_6821_);
lean_dec(v_a_6816_);
if (v_isShared_6820_ == 0)
{
lean_ctor_set(v___x_6819_, 0, v_path_6821_);
v___x_6823_ = v___x_6819_;
goto v_reusejp_6822_;
}
else
{
lean_object* v_reuseFailAlloc_6824_; 
v_reuseFailAlloc_6824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_path_6821_);
lean_ctor_set(v_reuseFailAlloc_6824_, 1, v_a_6817_);
v___x_6823_ = v_reuseFailAlloc_6824_;
goto v_reusejp_6822_;
}
v_reusejp_6822_:
{
return v___x_6823_;
}
}
}
else
{
lean_object* v_a_6826_; lean_object* v_a_6827_; lean_object* v___x_6829_; uint8_t v_isShared_6830_; uint8_t v_isSharedCheck_6834_; 
v_a_6826_ = lean_ctor_get(v___x_6815_, 0);
v_a_6827_ = lean_ctor_get(v___x_6815_, 1);
v_isSharedCheck_6834_ = !lean_is_exclusive(v___x_6815_);
if (v_isSharedCheck_6834_ == 0)
{
v___x_6829_ = v___x_6815_;
v_isShared_6830_ = v_isSharedCheck_6834_;
goto v_resetjp_6828_;
}
else
{
lean_inc(v_a_6827_);
lean_inc(v_a_6826_);
lean_dec(v___x_6815_);
v___x_6829_ = lean_box(0);
v_isShared_6830_ = v_isSharedCheck_6834_;
goto v_resetjp_6828_;
}
v_resetjp_6828_:
{
lean_object* v___x_6832_; 
if (v_isShared_6830_ == 0)
{
v___x_6832_ = v___x_6829_;
goto v_reusejp_6831_;
}
else
{
lean_object* v_reuseFailAlloc_6833_; 
v_reuseFailAlloc_6833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6826_);
lean_ctor_set(v_reuseFailAlloc_6833_, 1, v_a_6827_);
v___x_6832_ = v_reuseFailAlloc_6833_;
goto v_reusejp_6831_;
}
v_reusejp_6831_:
{
return v___x_6832_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6848_, lean_object* v_traceArgs_6849_, lean_object* v_oFile_6850_, lean_object* v_leanIncludeDir_x3f_6851_, lean_object* v_srcFile_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_){
_start:
{
lean_object* v_res_6860_; 
v_res_6860_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6848_, v_traceArgs_6849_, v_oFile_6850_, v_leanIncludeDir_x3f_6851_, v_srcFile_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_);
lean_dec_ref(v___y_6857_);
lean_dec(v___y_6856_);
lean_dec(v___y_6855_);
lean_dec(v___y_6854_);
return v_res_6860_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6861_, lean_object* v_srcJob_6862_, lean_object* v_weakArgs_6863_, lean_object* v_traceArgs_6864_, lean_object* v_leanIncludeDir_x3f_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_){
_start:
{
lean_object* v___f_6873_; lean_object* v___x_6874_; lean_object* v___x_6875_; uint8_t v___x_6876_; lean_object* v___x_6877_; 
v___f_6873_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6873_, 0, v_weakArgs_6863_);
lean_closure_set(v___f_6873_, 1, v_traceArgs_6864_);
lean_closure_set(v___f_6873_, 2, v_oFile_6861_);
lean_closure_set(v___f_6873_, 3, v_leanIncludeDir_x3f_6865_);
v___x_6874_ = l_Lake_instDataKindFilePath;
v___x_6875_ = lean_unsigned_to_nat(0u);
v___x_6876_ = 0;
v___x_6877_ = l_Lake_Job_mapM___redArg(v___x_6874_, v_srcJob_6862_, v___f_6873_, v___x_6875_, v___x_6876_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
return v___x_6877_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6878_, lean_object* v_srcJob_6879_, lean_object* v_weakArgs_6880_, lean_object* v_traceArgs_6881_, lean_object* v_leanIncludeDir_x3f_6882_, lean_object* v_a_6883_, lean_object* v_a_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_, lean_object* v_a_6887_, lean_object* v_a_6888_, lean_object* v_a_6889_){
_start:
{
lean_object* v_res_6890_; 
v_res_6890_ = l_Lake_buildLeanO(v_oFile_6878_, v_srcJob_6879_, v_weakArgs_6880_, v_traceArgs_6881_, v_leanIncludeDir_x3f_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_);
lean_dec_ref(v_a_6888_);
lean_dec_ref(v_a_6887_);
lean_dec(v_a_6886_);
lean_dec(v_a_6885_);
lean_dec(v_a_6884_);
return v_res_6890_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6891_, lean_object* v_oFiles_6892_, uint8_t v_thin_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_){
_start:
{
lean_object* v_toContext_6901_; lean_object* v_lakeEnv_6902_; lean_object* v_lean_6903_; lean_object* v_log_6904_; uint8_t v_action_6905_; uint8_t v_wantsRebuild_6906_; lean_object* v_trace_6907_; lean_object* v_buildTime_6908_; lean_object* v___x_6910_; uint8_t v_isShared_6911_; uint8_t v_isSharedCheck_6938_; 
v_toContext_6901_ = lean_ctor_get(v___y_6898_, 1);
v_lakeEnv_6902_ = lean_ctor_get(v_toContext_6901_, 0);
v_lean_6903_ = lean_ctor_get(v_lakeEnv_6902_, 1);
v_log_6904_ = lean_ctor_get(v___y_6899_, 0);
v_action_6905_ = lean_ctor_get_uint8(v___y_6899_, sizeof(void*)*3);
v_wantsRebuild_6906_ = lean_ctor_get_uint8(v___y_6899_, sizeof(void*)*3 + 1);
v_trace_6907_ = lean_ctor_get(v___y_6899_, 1);
v_buildTime_6908_ = lean_ctor_get(v___y_6899_, 2);
v_isSharedCheck_6938_ = !lean_is_exclusive(v___y_6899_);
if (v_isSharedCheck_6938_ == 0)
{
v___x_6910_ = v___y_6899_;
v_isShared_6911_ = v_isSharedCheck_6938_;
goto v_resetjp_6909_;
}
else
{
lean_inc(v_buildTime_6908_);
lean_inc(v_trace_6907_);
lean_inc(v_log_6904_);
lean_dec(v___y_6899_);
v___x_6910_ = lean_box(0);
v_isShared_6911_ = v_isSharedCheck_6938_;
goto v_resetjp_6909_;
}
v_resetjp_6909_:
{
lean_object* v_ar_6912_; lean_object* v___x_6913_; 
v_ar_6912_ = lean_ctor_get(v_lean_6903_, 13);
lean_inc_ref(v_ar_6912_);
v___x_6913_ = l_Lake_compileStaticLib(v_libFile_6891_, v_oFiles_6892_, v_ar_6912_, v_thin_6893_, v_log_6904_);
if (lean_obj_tag(v___x_6913_) == 0)
{
lean_object* v_a_6914_; lean_object* v_a_6915_; lean_object* v___x_6917_; uint8_t v_isShared_6918_; uint8_t v_isSharedCheck_6925_; 
v_a_6914_ = lean_ctor_get(v___x_6913_, 0);
v_a_6915_ = lean_ctor_get(v___x_6913_, 1);
v_isSharedCheck_6925_ = !lean_is_exclusive(v___x_6913_);
if (v_isSharedCheck_6925_ == 0)
{
v___x_6917_ = v___x_6913_;
v_isShared_6918_ = v_isSharedCheck_6925_;
goto v_resetjp_6916_;
}
else
{
lean_inc(v_a_6915_);
lean_inc(v_a_6914_);
lean_dec(v___x_6913_);
v___x_6917_ = lean_box(0);
v_isShared_6918_ = v_isSharedCheck_6925_;
goto v_resetjp_6916_;
}
v_resetjp_6916_:
{
lean_object* v___x_6920_; 
if (v_isShared_6911_ == 0)
{
lean_ctor_set(v___x_6910_, 0, v_a_6915_);
v___x_6920_ = v___x_6910_;
goto v_reusejp_6919_;
}
else
{
lean_object* v_reuseFailAlloc_6924_; 
v_reuseFailAlloc_6924_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6915_);
lean_ctor_set(v_reuseFailAlloc_6924_, 1, v_trace_6907_);
lean_ctor_set(v_reuseFailAlloc_6924_, 2, v_buildTime_6908_);
lean_ctor_set_uint8(v_reuseFailAlloc_6924_, sizeof(void*)*3, v_action_6905_);
lean_ctor_set_uint8(v_reuseFailAlloc_6924_, sizeof(void*)*3 + 1, v_wantsRebuild_6906_);
v___x_6920_ = v_reuseFailAlloc_6924_;
goto v_reusejp_6919_;
}
v_reusejp_6919_:
{
lean_object* v___x_6922_; 
if (v_isShared_6918_ == 0)
{
lean_ctor_set(v___x_6917_, 1, v___x_6920_);
v___x_6922_ = v___x_6917_;
goto v_reusejp_6921_;
}
else
{
lean_object* v_reuseFailAlloc_6923_; 
v_reuseFailAlloc_6923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6914_);
lean_ctor_set(v_reuseFailAlloc_6923_, 1, v___x_6920_);
v___x_6922_ = v_reuseFailAlloc_6923_;
goto v_reusejp_6921_;
}
v_reusejp_6921_:
{
return v___x_6922_;
}
}
}
}
else
{
lean_object* v_a_6926_; lean_object* v_a_6927_; lean_object* v___x_6929_; uint8_t v_isShared_6930_; uint8_t v_isSharedCheck_6937_; 
v_a_6926_ = lean_ctor_get(v___x_6913_, 0);
v_a_6927_ = lean_ctor_get(v___x_6913_, 1);
v_isSharedCheck_6937_ = !lean_is_exclusive(v___x_6913_);
if (v_isSharedCheck_6937_ == 0)
{
v___x_6929_ = v___x_6913_;
v_isShared_6930_ = v_isSharedCheck_6937_;
goto v_resetjp_6928_;
}
else
{
lean_inc(v_a_6927_);
lean_inc(v_a_6926_);
lean_dec(v___x_6913_);
v___x_6929_ = lean_box(0);
v_isShared_6930_ = v_isSharedCheck_6937_;
goto v_resetjp_6928_;
}
v_resetjp_6928_:
{
lean_object* v___x_6932_; 
if (v_isShared_6911_ == 0)
{
lean_ctor_set(v___x_6910_, 0, v_a_6927_);
v___x_6932_ = v___x_6910_;
goto v_reusejp_6931_;
}
else
{
lean_object* v_reuseFailAlloc_6936_; 
v_reuseFailAlloc_6936_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6936_, 0, v_a_6927_);
lean_ctor_set(v_reuseFailAlloc_6936_, 1, v_trace_6907_);
lean_ctor_set(v_reuseFailAlloc_6936_, 2, v_buildTime_6908_);
lean_ctor_set_uint8(v_reuseFailAlloc_6936_, sizeof(void*)*3, v_action_6905_);
lean_ctor_set_uint8(v_reuseFailAlloc_6936_, sizeof(void*)*3 + 1, v_wantsRebuild_6906_);
v___x_6932_ = v_reuseFailAlloc_6936_;
goto v_reusejp_6931_;
}
v_reusejp_6931_:
{
lean_object* v___x_6934_; 
if (v_isShared_6930_ == 0)
{
lean_ctor_set(v___x_6929_, 1, v___x_6932_);
v___x_6934_ = v___x_6929_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6935_; 
v_reuseFailAlloc_6935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_a_6926_);
lean_ctor_set(v_reuseFailAlloc_6935_, 1, v___x_6932_);
v___x_6934_ = v_reuseFailAlloc_6935_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
return v___x_6934_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6939_, lean_object* v_oFiles_6940_, lean_object* v_thin_6941_, lean_object* v___y_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_){
_start:
{
uint8_t v_thin_boxed_6949_; lean_object* v_res_6950_; 
v_thin_boxed_6949_ = lean_unbox(v_thin_6941_);
v_res_6950_ = l_Lake_buildStaticLib___lam__0(v_libFile_6939_, v_oFiles_6940_, v_thin_boxed_6949_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
lean_dec_ref(v___y_6946_);
lean_dec(v___y_6945_);
lean_dec(v___y_6944_);
lean_dec(v___y_6943_);
lean_dec_ref(v___y_6942_);
return v_res_6950_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6952_, uint8_t v_thin_6953_, lean_object* v_oFiles_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_, lean_object* v___y_6960_){
_start:
{
lean_object* v___x_6962_; lean_object* v___f_6963_; uint8_t v___x_6964_; lean_object* v___x_6965_; uint8_t v___x_6966_; lean_object* v___x_6967_; 
v___x_6962_ = lean_box(v_thin_6953_);
lean_inc_ref(v_libFile_6952_);
v___f_6963_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6963_, 0, v_libFile_6952_);
lean_closure_set(v___f_6963_, 1, v_oFiles_6954_);
lean_closure_set(v___f_6963_, 2, v___x_6962_);
v___x_6964_ = 0;
v___x_6965_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6966_ = 1;
v___x_6967_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6952_, v___f_6963_, v___x_6964_, v___x_6965_, v___x_6966_, v___x_6964_, v___x_6964_, v___y_6955_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
if (lean_obj_tag(v___x_6967_) == 0)
{
lean_object* v_a_6968_; lean_object* v_a_6969_; lean_object* v___x_6971_; uint8_t v_isShared_6972_; uint8_t v_isSharedCheck_6977_; 
v_a_6968_ = lean_ctor_get(v___x_6967_, 0);
v_a_6969_ = lean_ctor_get(v___x_6967_, 1);
v_isSharedCheck_6977_ = !lean_is_exclusive(v___x_6967_);
if (v_isSharedCheck_6977_ == 0)
{
v___x_6971_ = v___x_6967_;
v_isShared_6972_ = v_isSharedCheck_6977_;
goto v_resetjp_6970_;
}
else
{
lean_inc(v_a_6969_);
lean_inc(v_a_6968_);
lean_dec(v___x_6967_);
v___x_6971_ = lean_box(0);
v_isShared_6972_ = v_isSharedCheck_6977_;
goto v_resetjp_6970_;
}
v_resetjp_6970_:
{
lean_object* v_path_6973_; lean_object* v___x_6975_; 
v_path_6973_ = lean_ctor_get(v_a_6968_, 1);
lean_inc_ref(v_path_6973_);
lean_dec(v_a_6968_);
if (v_isShared_6972_ == 0)
{
lean_ctor_set(v___x_6971_, 0, v_path_6973_);
v___x_6975_ = v___x_6971_;
goto v_reusejp_6974_;
}
else
{
lean_object* v_reuseFailAlloc_6976_; 
v_reuseFailAlloc_6976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6976_, 0, v_path_6973_);
lean_ctor_set(v_reuseFailAlloc_6976_, 1, v_a_6969_);
v___x_6975_ = v_reuseFailAlloc_6976_;
goto v_reusejp_6974_;
}
v_reusejp_6974_:
{
return v___x_6975_;
}
}
}
else
{
lean_object* v_a_6978_; lean_object* v_a_6979_; lean_object* v___x_6981_; uint8_t v_isShared_6982_; uint8_t v_isSharedCheck_6986_; 
v_a_6978_ = lean_ctor_get(v___x_6967_, 0);
v_a_6979_ = lean_ctor_get(v___x_6967_, 1);
v_isSharedCheck_6986_ = !lean_is_exclusive(v___x_6967_);
if (v_isSharedCheck_6986_ == 0)
{
v___x_6981_ = v___x_6967_;
v_isShared_6982_ = v_isSharedCheck_6986_;
goto v_resetjp_6980_;
}
else
{
lean_inc(v_a_6979_);
lean_inc(v_a_6978_);
lean_dec(v___x_6967_);
v___x_6981_ = lean_box(0);
v_isShared_6982_ = v_isSharedCheck_6986_;
goto v_resetjp_6980_;
}
v_resetjp_6980_:
{
lean_object* v___x_6984_; 
if (v_isShared_6982_ == 0)
{
v___x_6984_ = v___x_6981_;
goto v_reusejp_6983_;
}
else
{
lean_object* v_reuseFailAlloc_6985_; 
v_reuseFailAlloc_6985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6985_, 0, v_a_6978_);
lean_ctor_set(v_reuseFailAlloc_6985_, 1, v_a_6979_);
v___x_6984_ = v_reuseFailAlloc_6985_;
goto v_reusejp_6983_;
}
v_reusejp_6983_:
{
return v___x_6984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6987_, lean_object* v_thin_6988_, lean_object* v_oFiles_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_){
_start:
{
uint8_t v_thin_boxed_6997_; lean_object* v_res_6998_; 
v_thin_boxed_6997_ = lean_unbox(v_thin_6988_);
v_res_6998_ = l_Lake_buildStaticLib___lam__1(v_libFile_6987_, v_thin_boxed_6997_, v_oFiles_6989_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_);
lean_dec_ref(v___y_6994_);
lean_dec(v___y_6993_);
lean_dec(v___y_6992_);
lean_dec(v___y_6991_);
return v_res_6998_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_7000_, lean_object* v_oFileJobs_7001_, uint8_t v_thin_7002_, lean_object* v_a_7003_, lean_object* v_a_7004_, lean_object* v_a_7005_, lean_object* v_a_7006_, lean_object* v_a_7007_, lean_object* v_a_7008_){
_start:
{
lean_object* v___x_7010_; lean_object* v___f_7011_; lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7014_; lean_object* v___x_7015_; uint8_t v___x_7016_; lean_object* v___x_7017_; 
v___x_7010_ = lean_box(v_thin_7002_);
v___f_7011_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_7011_, 0, v_libFile_7000_);
lean_closure_set(v___f_7011_, 1, v___x_7010_);
v___x_7012_ = l_Lake_instDataKindFilePath;
v___x_7013_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_7014_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_7001_, v___x_7013_);
v___x_7015_ = lean_unsigned_to_nat(0u);
v___x_7016_ = 0;
v___x_7017_ = l_Lake_Job_mapM___redArg(v___x_7012_, v___x_7014_, v___f_7011_, v___x_7015_, v___x_7016_, v_a_7003_, v_a_7004_, v_a_7005_, v_a_7006_, v_a_7007_, v_a_7008_);
return v___x_7017_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_7018_, lean_object* v_oFileJobs_7019_, lean_object* v_thin_7020_, lean_object* v_a_7021_, lean_object* v_a_7022_, lean_object* v_a_7023_, lean_object* v_a_7024_, lean_object* v_a_7025_, lean_object* v_a_7026_, lean_object* v_a_7027_){
_start:
{
uint8_t v_thin_boxed_7028_; lean_object* v_res_7029_; 
v_thin_boxed_7028_ = lean_unbox(v_thin_7020_);
v_res_7029_ = l_Lake_buildStaticLib(v_libFile_7018_, v_oFileJobs_7019_, v_thin_boxed_7028_, v_a_7021_, v_a_7022_, v_a_7023_, v_a_7024_, v_a_7025_, v_a_7026_);
lean_dec_ref(v_a_7026_);
lean_dec_ref(v_a_7025_);
lean_dec(v_a_7024_);
lean_dec(v_a_7023_);
lean_dec(v_a_7022_);
lean_dec_ref(v_oFileJobs_7019_);
return v_res_7029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7030_, size_t v_sz_7031_, size_t v_i_7032_, lean_object* v_b_7033_){
_start:
{
uint8_t v___x_7034_; 
v___x_7034_ = lean_usize_dec_lt(v_i_7032_, v_sz_7031_);
if (v___x_7034_ == 0)
{
return v_b_7033_;
}
else
{
lean_object* v_a_7035_; lean_object* v___x_7036_; size_t v___x_7037_; size_t v___x_7038_; 
v_a_7035_ = lean_array_uget_borrowed(v_as_7030_, v_i_7032_);
lean_inc(v_a_7035_);
v___x_7036_ = lean_array_push(v_b_7033_, v_a_7035_);
v___x_7037_ = ((size_t)1ULL);
v___x_7038_ = lean_usize_add(v_i_7032_, v___x_7037_);
v_i_7032_ = v___x_7038_;
v_b_7033_ = v___x_7036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7040_, lean_object* v_sz_7041_, lean_object* v_i_7042_, lean_object* v_b_7043_){
_start:
{
size_t v_sz_boxed_7044_; size_t v_i_boxed_7045_; lean_object* v_res_7046_; 
v_sz_boxed_7044_ = lean_unbox_usize(v_sz_7041_);
lean_dec(v_sz_7041_);
v_i_boxed_7045_ = lean_unbox_usize(v_i_7042_);
lean_dec(v_i_7042_);
v_res_7046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7040_, v_sz_boxed_7044_, v_i_boxed_7045_, v_b_7043_);
lean_dec_ref(v_as_7040_);
return v_res_7046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7049_, size_t v_sz_7050_, size_t v_i_7051_, lean_object* v_b_7052_){
_start:
{
uint8_t v___x_7053_; 
v___x_7053_ = lean_usize_dec_lt(v_i_7051_, v_sz_7050_);
if (v___x_7053_ == 0)
{
return v_b_7052_;
}
else
{
lean_object* v_a_7054_; lean_object* v_args_7056_; lean_object* v___x_7064_; 
v_a_7054_ = lean_array_uget_borrowed(v_as_7049_, v_i_7051_);
lean_inc(v_a_7054_);
v___x_7064_ = l_Lake_Dynlib_dir_x3f(v_a_7054_);
if (lean_obj_tag(v___x_7064_) == 1)
{
lean_object* v_val_7065_; lean_object* v___x_7066_; lean_object* v___x_7067_; lean_object* v___x_7068_; 
v_val_7065_ = lean_ctor_get(v___x_7064_, 0);
lean_inc(v_val_7065_);
lean_dec_ref_known(v___x_7064_, 1);
v___x_7066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7067_ = lean_string_append(v___x_7066_, v_val_7065_);
lean_dec(v_val_7065_);
v___x_7068_ = lean_array_push(v_b_7052_, v___x_7067_);
v_args_7056_ = v___x_7068_;
goto v___jp_7055_;
}
else
{
lean_dec(v___x_7064_);
v_args_7056_ = v_b_7052_;
goto v___jp_7055_;
}
v___jp_7055_:
{
lean_object* v_name_7057_; lean_object* v___x_7058_; lean_object* v___x_7059_; lean_object* v___x_7060_; size_t v___x_7061_; size_t v___x_7062_; 
v_name_7057_ = lean_ctor_get(v_a_7054_, 1);
v___x_7058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7059_ = lean_string_append(v___x_7058_, v_name_7057_);
v___x_7060_ = lean_array_push(v_args_7056_, v___x_7059_);
v___x_7061_ = ((size_t)1ULL);
v___x_7062_ = lean_usize_add(v_i_7051_, v___x_7061_);
v_i_7051_ = v___x_7062_;
v_b_7052_ = v___x_7060_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7069_, lean_object* v_sz_7070_, lean_object* v_i_7071_, lean_object* v_b_7072_){
_start:
{
size_t v_sz_boxed_7073_; size_t v_i_boxed_7074_; lean_object* v_res_7075_; 
v_sz_boxed_7073_ = lean_unbox_usize(v_sz_7070_);
lean_dec(v_sz_7070_);
v_i_boxed_7074_ = lean_unbox_usize(v_i_7071_);
lean_dec(v_i_7071_);
v_res_7075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7069_, v_sz_boxed_7073_, v_i_boxed_7074_, v_b_7072_);
lean_dec_ref(v_as_7069_);
return v_res_7075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7076_, lean_object* v_libs_7077_){
_start:
{
lean_object* v_args_7078_; size_t v_sz_7079_; size_t v___x_7080_; lean_object* v___x_7081_; size_t v_sz_7082_; lean_object* v___x_7083_; 
v_args_7078_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7079_ = lean_array_size(v_objs_7076_);
v___x_7080_ = ((size_t)0ULL);
v___x_7081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7076_, v_sz_7079_, v___x_7080_, v_args_7078_);
v_sz_7082_ = lean_array_size(v_libs_7077_);
v___x_7083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7077_, v_sz_7082_, v___x_7080_, v___x_7081_);
return v___x_7083_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7084_, lean_object* v_libs_7085_){
_start:
{
lean_object* v_res_7086_; 
v_res_7086_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7084_, v_libs_7085_);
lean_dec_ref(v_libs_7085_);
lean_dec_ref(v_objs_7084_);
return v_res_7086_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7087_, lean_object* v_t_7088_){
_start:
{
if (lean_obj_tag(v_t_7088_) == 0)
{
lean_object* v_k_7089_; lean_object* v_l_7090_; lean_object* v_r_7091_; uint8_t v___x_7092_; 
v_k_7089_ = lean_ctor_get(v_t_7088_, 1);
v_l_7090_ = lean_ctor_get(v_t_7088_, 3);
v_r_7091_ = lean_ctor_get(v_t_7088_, 4);
v___x_7092_ = lean_string_compare(v_k_7087_, v_k_7089_);
switch(v___x_7092_)
{
case 0:
{
v_t_7088_ = v_l_7090_;
goto _start;
}
case 1:
{
uint8_t v___x_7094_; 
v___x_7094_ = 1;
return v___x_7094_;
}
default: 
{
v_t_7088_ = v_r_7091_;
goto _start;
}
}
}
else
{
uint8_t v___x_7096_; 
v___x_7096_ = 0;
return v___x_7096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7097_, lean_object* v_t_7098_){
_start:
{
uint8_t v_res_7099_; lean_object* v_r_7100_; 
v_res_7099_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7097_, v_t_7098_);
lean_dec(v_t_7098_);
lean_dec_ref(v_k_7097_);
v_r_7100_ = lean_box(v_res_7099_);
return v_r_7100_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7101_, lean_object* v_x_7102_){
_start:
{
if (lean_obj_tag(v_x_7102_) == 0)
{
uint8_t v___x_7103_; 
v___x_7103_ = 0;
return v___x_7103_;
}
else
{
lean_object* v_head_7104_; lean_object* v_tail_7105_; uint8_t v___x_7106_; 
v_head_7104_ = lean_ctor_get(v_x_7102_, 0);
v_tail_7105_ = lean_ctor_get(v_x_7102_, 1);
v___x_7106_ = lean_string_dec_eq(v_a_7101_, v_head_7104_);
if (v___x_7106_ == 0)
{
v_x_7102_ = v_tail_7105_;
goto _start;
}
else
{
return v___x_7106_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7108_, lean_object* v_x_7109_){
_start:
{
uint8_t v_res_7110_; lean_object* v_r_7111_; 
v_res_7110_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7108_, v_x_7109_);
lean_dec(v_x_7109_);
lean_dec_ref(v_a_7108_);
v_r_7111_ = lean_box(v_res_7110_);
return v_r_7111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7112_, lean_object* v_v_7113_, lean_object* v_t_7114_){
_start:
{
if (lean_obj_tag(v_t_7114_) == 0)
{
lean_object* v_size_7115_; lean_object* v_k_7116_; lean_object* v_v_7117_; lean_object* v_l_7118_; lean_object* v_r_7119_; lean_object* v___x_7121_; uint8_t v_isShared_7122_; uint8_t v_isSharedCheck_7399_; 
v_size_7115_ = lean_ctor_get(v_t_7114_, 0);
v_k_7116_ = lean_ctor_get(v_t_7114_, 1);
v_v_7117_ = lean_ctor_get(v_t_7114_, 2);
v_l_7118_ = lean_ctor_get(v_t_7114_, 3);
v_r_7119_ = lean_ctor_get(v_t_7114_, 4);
v_isSharedCheck_7399_ = !lean_is_exclusive(v_t_7114_);
if (v_isSharedCheck_7399_ == 0)
{
v___x_7121_ = v_t_7114_;
v_isShared_7122_ = v_isSharedCheck_7399_;
goto v_resetjp_7120_;
}
else
{
lean_inc(v_r_7119_);
lean_inc(v_l_7118_);
lean_inc(v_v_7117_);
lean_inc(v_k_7116_);
lean_inc(v_size_7115_);
lean_dec(v_t_7114_);
v___x_7121_ = lean_box(0);
v_isShared_7122_ = v_isSharedCheck_7399_;
goto v_resetjp_7120_;
}
v_resetjp_7120_:
{
uint8_t v___x_7123_; 
v___x_7123_ = lean_string_compare(v_k_7112_, v_k_7116_);
switch(v___x_7123_)
{
case 0:
{
lean_object* v_impl_7124_; lean_object* v___x_7125_; 
lean_dec(v_size_7115_);
v_impl_7124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7112_, v_v_7113_, v_l_7118_);
v___x_7125_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7119_) == 0)
{
lean_object* v_size_7126_; lean_object* v_size_7127_; lean_object* v_k_7128_; lean_object* v_v_7129_; lean_object* v_l_7130_; lean_object* v_r_7131_; lean_object* v___x_7132_; lean_object* v___x_7133_; uint8_t v___x_7134_; 
v_size_7126_ = lean_ctor_get(v_r_7119_, 0);
v_size_7127_ = lean_ctor_get(v_impl_7124_, 0);
lean_inc(v_size_7127_);
v_k_7128_ = lean_ctor_get(v_impl_7124_, 1);
lean_inc(v_k_7128_);
v_v_7129_ = lean_ctor_get(v_impl_7124_, 2);
lean_inc(v_v_7129_);
v_l_7130_ = lean_ctor_get(v_impl_7124_, 3);
lean_inc(v_l_7130_);
v_r_7131_ = lean_ctor_get(v_impl_7124_, 4);
lean_inc(v_r_7131_);
v___x_7132_ = lean_unsigned_to_nat(3u);
v___x_7133_ = lean_nat_mul(v___x_7132_, v_size_7126_);
v___x_7134_ = lean_nat_dec_lt(v___x_7133_, v_size_7127_);
lean_dec(v___x_7133_);
if (v___x_7134_ == 0)
{
lean_object* v___x_7135_; lean_object* v___x_7136_; lean_object* v___x_7138_; 
lean_dec(v_r_7131_);
lean_dec(v_l_7130_);
lean_dec(v_v_7129_);
lean_dec(v_k_7128_);
v___x_7135_ = lean_nat_add(v___x_7125_, v_size_7127_);
lean_dec(v_size_7127_);
v___x_7136_ = lean_nat_add(v___x_7135_, v_size_7126_);
lean_dec(v___x_7135_);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 3, v_impl_7124_);
lean_ctor_set(v___x_7121_, 0, v___x_7136_);
v___x_7138_ = v___x_7121_;
goto v_reusejp_7137_;
}
else
{
lean_object* v_reuseFailAlloc_7139_; 
v_reuseFailAlloc_7139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7139_, 0, v___x_7136_);
lean_ctor_set(v_reuseFailAlloc_7139_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7139_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7139_, 3, v_impl_7124_);
lean_ctor_set(v_reuseFailAlloc_7139_, 4, v_r_7119_);
v___x_7138_ = v_reuseFailAlloc_7139_;
goto v_reusejp_7137_;
}
v_reusejp_7137_:
{
return v___x_7138_;
}
}
else
{
lean_object* v___x_7141_; uint8_t v_isShared_7142_; uint8_t v_isSharedCheck_7205_; 
v_isSharedCheck_7205_ = !lean_is_exclusive(v_impl_7124_);
if (v_isSharedCheck_7205_ == 0)
{
lean_object* v_unused_7206_; lean_object* v_unused_7207_; lean_object* v_unused_7208_; lean_object* v_unused_7209_; lean_object* v_unused_7210_; 
v_unused_7206_ = lean_ctor_get(v_impl_7124_, 4);
lean_dec(v_unused_7206_);
v_unused_7207_ = lean_ctor_get(v_impl_7124_, 3);
lean_dec(v_unused_7207_);
v_unused_7208_ = lean_ctor_get(v_impl_7124_, 2);
lean_dec(v_unused_7208_);
v_unused_7209_ = lean_ctor_get(v_impl_7124_, 1);
lean_dec(v_unused_7209_);
v_unused_7210_ = lean_ctor_get(v_impl_7124_, 0);
lean_dec(v_unused_7210_);
v___x_7141_ = v_impl_7124_;
v_isShared_7142_ = v_isSharedCheck_7205_;
goto v_resetjp_7140_;
}
else
{
lean_dec(v_impl_7124_);
v___x_7141_ = lean_box(0);
v_isShared_7142_ = v_isSharedCheck_7205_;
goto v_resetjp_7140_;
}
v_resetjp_7140_:
{
lean_object* v_size_7143_; lean_object* v_size_7144_; lean_object* v_k_7145_; lean_object* v_v_7146_; lean_object* v_l_7147_; lean_object* v_r_7148_; lean_object* v___x_7149_; lean_object* v___x_7150_; uint8_t v___x_7151_; 
v_size_7143_ = lean_ctor_get(v_l_7130_, 0);
v_size_7144_ = lean_ctor_get(v_r_7131_, 0);
v_k_7145_ = lean_ctor_get(v_r_7131_, 1);
v_v_7146_ = lean_ctor_get(v_r_7131_, 2);
v_l_7147_ = lean_ctor_get(v_r_7131_, 3);
v_r_7148_ = lean_ctor_get(v_r_7131_, 4);
v___x_7149_ = lean_unsigned_to_nat(2u);
v___x_7150_ = lean_nat_mul(v___x_7149_, v_size_7143_);
v___x_7151_ = lean_nat_dec_lt(v_size_7144_, v___x_7150_);
lean_dec(v___x_7150_);
if (v___x_7151_ == 0)
{
lean_object* v___x_7153_; uint8_t v_isShared_7154_; uint8_t v_isSharedCheck_7180_; 
lean_inc(v_r_7148_);
lean_inc(v_l_7147_);
lean_inc(v_v_7146_);
lean_inc(v_k_7145_);
v_isSharedCheck_7180_ = !lean_is_exclusive(v_r_7131_);
if (v_isSharedCheck_7180_ == 0)
{
lean_object* v_unused_7181_; lean_object* v_unused_7182_; lean_object* v_unused_7183_; lean_object* v_unused_7184_; lean_object* v_unused_7185_; 
v_unused_7181_ = lean_ctor_get(v_r_7131_, 4);
lean_dec(v_unused_7181_);
v_unused_7182_ = lean_ctor_get(v_r_7131_, 3);
lean_dec(v_unused_7182_);
v_unused_7183_ = lean_ctor_get(v_r_7131_, 2);
lean_dec(v_unused_7183_);
v_unused_7184_ = lean_ctor_get(v_r_7131_, 1);
lean_dec(v_unused_7184_);
v_unused_7185_ = lean_ctor_get(v_r_7131_, 0);
lean_dec(v_unused_7185_);
v___x_7153_ = v_r_7131_;
v_isShared_7154_ = v_isSharedCheck_7180_;
goto v_resetjp_7152_;
}
else
{
lean_dec(v_r_7131_);
v___x_7153_ = lean_box(0);
v_isShared_7154_ = v_isSharedCheck_7180_;
goto v_resetjp_7152_;
}
v_resetjp_7152_:
{
lean_object* v___x_7155_; lean_object* v___x_7156_; lean_object* v___y_7158_; lean_object* v___y_7159_; lean_object* v___y_7160_; lean_object* v___x_7168_; lean_object* v___y_7170_; 
v___x_7155_ = lean_nat_add(v___x_7125_, v_size_7127_);
lean_dec(v_size_7127_);
v___x_7156_ = lean_nat_add(v___x_7155_, v_size_7126_);
lean_dec(v___x_7155_);
v___x_7168_ = lean_nat_add(v___x_7125_, v_size_7143_);
if (lean_obj_tag(v_l_7147_) == 0)
{
lean_object* v_size_7178_; 
v_size_7178_ = lean_ctor_get(v_l_7147_, 0);
lean_inc(v_size_7178_);
v___y_7170_ = v_size_7178_;
goto v___jp_7169_;
}
else
{
lean_object* v___x_7179_; 
v___x_7179_ = lean_unsigned_to_nat(0u);
v___y_7170_ = v___x_7179_;
goto v___jp_7169_;
}
v___jp_7157_:
{
lean_object* v___x_7161_; lean_object* v___x_7163_; 
v___x_7161_ = lean_nat_add(v___y_7158_, v___y_7160_);
lean_dec(v___y_7160_);
lean_dec(v___y_7158_);
if (v_isShared_7154_ == 0)
{
lean_ctor_set(v___x_7153_, 4, v_r_7119_);
lean_ctor_set(v___x_7153_, 3, v_r_7148_);
lean_ctor_set(v___x_7153_, 2, v_v_7117_);
lean_ctor_set(v___x_7153_, 1, v_k_7116_);
lean_ctor_set(v___x_7153_, 0, v___x_7161_);
v___x_7163_ = v___x_7153_;
goto v_reusejp_7162_;
}
else
{
lean_object* v_reuseFailAlloc_7167_; 
v_reuseFailAlloc_7167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7167_, 0, v___x_7161_);
lean_ctor_set(v_reuseFailAlloc_7167_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7167_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7167_, 3, v_r_7148_);
lean_ctor_set(v_reuseFailAlloc_7167_, 4, v_r_7119_);
v___x_7163_ = v_reuseFailAlloc_7167_;
goto v_reusejp_7162_;
}
v_reusejp_7162_:
{
lean_object* v___x_7165_; 
if (v_isShared_7142_ == 0)
{
lean_ctor_set(v___x_7141_, 4, v___x_7163_);
lean_ctor_set(v___x_7141_, 3, v___y_7159_);
lean_ctor_set(v___x_7141_, 2, v_v_7146_);
lean_ctor_set(v___x_7141_, 1, v_k_7145_);
lean_ctor_set(v___x_7141_, 0, v___x_7156_);
v___x_7165_ = v___x_7141_;
goto v_reusejp_7164_;
}
else
{
lean_object* v_reuseFailAlloc_7166_; 
v_reuseFailAlloc_7166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7166_, 0, v___x_7156_);
lean_ctor_set(v_reuseFailAlloc_7166_, 1, v_k_7145_);
lean_ctor_set(v_reuseFailAlloc_7166_, 2, v_v_7146_);
lean_ctor_set(v_reuseFailAlloc_7166_, 3, v___y_7159_);
lean_ctor_set(v_reuseFailAlloc_7166_, 4, v___x_7163_);
v___x_7165_ = v_reuseFailAlloc_7166_;
goto v_reusejp_7164_;
}
v_reusejp_7164_:
{
return v___x_7165_;
}
}
}
v___jp_7169_:
{
lean_object* v___x_7171_; lean_object* v___x_7173_; 
v___x_7171_ = lean_nat_add(v___x_7168_, v___y_7170_);
lean_dec(v___y_7170_);
lean_dec(v___x_7168_);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_l_7147_);
lean_ctor_set(v___x_7121_, 3, v_l_7130_);
lean_ctor_set(v___x_7121_, 2, v_v_7129_);
lean_ctor_set(v___x_7121_, 1, v_k_7128_);
lean_ctor_set(v___x_7121_, 0, v___x_7171_);
v___x_7173_ = v___x_7121_;
goto v_reusejp_7172_;
}
else
{
lean_object* v_reuseFailAlloc_7177_; 
v_reuseFailAlloc_7177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7177_, 0, v___x_7171_);
lean_ctor_set(v_reuseFailAlloc_7177_, 1, v_k_7128_);
lean_ctor_set(v_reuseFailAlloc_7177_, 2, v_v_7129_);
lean_ctor_set(v_reuseFailAlloc_7177_, 3, v_l_7130_);
lean_ctor_set(v_reuseFailAlloc_7177_, 4, v_l_7147_);
v___x_7173_ = v_reuseFailAlloc_7177_;
goto v_reusejp_7172_;
}
v_reusejp_7172_:
{
lean_object* v___x_7174_; 
v___x_7174_ = lean_nat_add(v___x_7125_, v_size_7126_);
if (lean_obj_tag(v_r_7148_) == 0)
{
lean_object* v_size_7175_; 
v_size_7175_ = lean_ctor_get(v_r_7148_, 0);
lean_inc(v_size_7175_);
v___y_7158_ = v___x_7174_;
v___y_7159_ = v___x_7173_;
v___y_7160_ = v_size_7175_;
goto v___jp_7157_;
}
else
{
lean_object* v___x_7176_; 
v___x_7176_ = lean_unsigned_to_nat(0u);
v___y_7158_ = v___x_7174_;
v___y_7159_ = v___x_7173_;
v___y_7160_ = v___x_7176_;
goto v___jp_7157_;
}
}
}
}
}
else
{
lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7189_; lean_object* v___x_7191_; 
lean_del_object(v___x_7121_);
v___x_7186_ = lean_nat_add(v___x_7125_, v_size_7127_);
lean_dec(v_size_7127_);
v___x_7187_ = lean_nat_add(v___x_7186_, v_size_7126_);
lean_dec(v___x_7186_);
v___x_7188_ = lean_nat_add(v___x_7125_, v_size_7126_);
v___x_7189_ = lean_nat_add(v___x_7188_, v_size_7144_);
lean_dec(v___x_7188_);
lean_inc_ref(v_r_7119_);
if (v_isShared_7142_ == 0)
{
lean_ctor_set(v___x_7141_, 4, v_r_7119_);
lean_ctor_set(v___x_7141_, 3, v_r_7131_);
lean_ctor_set(v___x_7141_, 2, v_v_7117_);
lean_ctor_set(v___x_7141_, 1, v_k_7116_);
lean_ctor_set(v___x_7141_, 0, v___x_7189_);
v___x_7191_ = v___x_7141_;
goto v_reusejp_7190_;
}
else
{
lean_object* v_reuseFailAlloc_7204_; 
v_reuseFailAlloc_7204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7204_, 0, v___x_7189_);
lean_ctor_set(v_reuseFailAlloc_7204_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7204_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7204_, 3, v_r_7131_);
lean_ctor_set(v_reuseFailAlloc_7204_, 4, v_r_7119_);
v___x_7191_ = v_reuseFailAlloc_7204_;
goto v_reusejp_7190_;
}
v_reusejp_7190_:
{
lean_object* v___x_7193_; uint8_t v_isShared_7194_; uint8_t v_isSharedCheck_7198_; 
v_isSharedCheck_7198_ = !lean_is_exclusive(v_r_7119_);
if (v_isSharedCheck_7198_ == 0)
{
lean_object* v_unused_7199_; lean_object* v_unused_7200_; lean_object* v_unused_7201_; lean_object* v_unused_7202_; lean_object* v_unused_7203_; 
v_unused_7199_ = lean_ctor_get(v_r_7119_, 4);
lean_dec(v_unused_7199_);
v_unused_7200_ = lean_ctor_get(v_r_7119_, 3);
lean_dec(v_unused_7200_);
v_unused_7201_ = lean_ctor_get(v_r_7119_, 2);
lean_dec(v_unused_7201_);
v_unused_7202_ = lean_ctor_get(v_r_7119_, 1);
lean_dec(v_unused_7202_);
v_unused_7203_ = lean_ctor_get(v_r_7119_, 0);
lean_dec(v_unused_7203_);
v___x_7193_ = v_r_7119_;
v_isShared_7194_ = v_isSharedCheck_7198_;
goto v_resetjp_7192_;
}
else
{
lean_dec(v_r_7119_);
v___x_7193_ = lean_box(0);
v_isShared_7194_ = v_isSharedCheck_7198_;
goto v_resetjp_7192_;
}
v_resetjp_7192_:
{
lean_object* v___x_7196_; 
if (v_isShared_7194_ == 0)
{
lean_ctor_set(v___x_7193_, 4, v___x_7191_);
lean_ctor_set(v___x_7193_, 3, v_l_7130_);
lean_ctor_set(v___x_7193_, 2, v_v_7129_);
lean_ctor_set(v___x_7193_, 1, v_k_7128_);
lean_ctor_set(v___x_7193_, 0, v___x_7187_);
v___x_7196_ = v___x_7193_;
goto v_reusejp_7195_;
}
else
{
lean_object* v_reuseFailAlloc_7197_; 
v_reuseFailAlloc_7197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7197_, 0, v___x_7187_);
lean_ctor_set(v_reuseFailAlloc_7197_, 1, v_k_7128_);
lean_ctor_set(v_reuseFailAlloc_7197_, 2, v_v_7129_);
lean_ctor_set(v_reuseFailAlloc_7197_, 3, v_l_7130_);
lean_ctor_set(v_reuseFailAlloc_7197_, 4, v___x_7191_);
v___x_7196_ = v_reuseFailAlloc_7197_;
goto v_reusejp_7195_;
}
v_reusejp_7195_:
{
return v___x_7196_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7211_; 
v_l_7211_ = lean_ctor_get(v_impl_7124_, 3);
lean_inc(v_l_7211_);
if (lean_obj_tag(v_l_7211_) == 0)
{
lean_object* v_r_7212_; lean_object* v_k_7213_; lean_object* v_v_7214_; lean_object* v___x_7216_; uint8_t v_isShared_7217_; uint8_t v_isSharedCheck_7225_; 
v_r_7212_ = lean_ctor_get(v_impl_7124_, 4);
v_k_7213_ = lean_ctor_get(v_impl_7124_, 1);
v_v_7214_ = lean_ctor_get(v_impl_7124_, 2);
v_isSharedCheck_7225_ = !lean_is_exclusive(v_impl_7124_);
if (v_isSharedCheck_7225_ == 0)
{
lean_object* v_unused_7226_; lean_object* v_unused_7227_; 
v_unused_7226_ = lean_ctor_get(v_impl_7124_, 3);
lean_dec(v_unused_7226_);
v_unused_7227_ = lean_ctor_get(v_impl_7124_, 0);
lean_dec(v_unused_7227_);
v___x_7216_ = v_impl_7124_;
v_isShared_7217_ = v_isSharedCheck_7225_;
goto v_resetjp_7215_;
}
else
{
lean_inc(v_r_7212_);
lean_inc(v_v_7214_);
lean_inc(v_k_7213_);
lean_dec(v_impl_7124_);
v___x_7216_ = lean_box(0);
v_isShared_7217_ = v_isSharedCheck_7225_;
goto v_resetjp_7215_;
}
v_resetjp_7215_:
{
lean_object* v___x_7218_; lean_object* v___x_7220_; 
v___x_7218_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7212_);
if (v_isShared_7217_ == 0)
{
lean_ctor_set(v___x_7216_, 3, v_r_7212_);
lean_ctor_set(v___x_7216_, 2, v_v_7117_);
lean_ctor_set(v___x_7216_, 1, v_k_7116_);
lean_ctor_set(v___x_7216_, 0, v___x_7125_);
v___x_7220_ = v___x_7216_;
goto v_reusejp_7219_;
}
else
{
lean_object* v_reuseFailAlloc_7224_; 
v_reuseFailAlloc_7224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7224_, 0, v___x_7125_);
lean_ctor_set(v_reuseFailAlloc_7224_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7224_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7224_, 3, v_r_7212_);
lean_ctor_set(v_reuseFailAlloc_7224_, 4, v_r_7212_);
v___x_7220_ = v_reuseFailAlloc_7224_;
goto v_reusejp_7219_;
}
v_reusejp_7219_:
{
lean_object* v___x_7222_; 
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v___x_7220_);
lean_ctor_set(v___x_7121_, 3, v_l_7211_);
lean_ctor_set(v___x_7121_, 2, v_v_7214_);
lean_ctor_set(v___x_7121_, 1, v_k_7213_);
lean_ctor_set(v___x_7121_, 0, v___x_7218_);
v___x_7222_ = v___x_7121_;
goto v_reusejp_7221_;
}
else
{
lean_object* v_reuseFailAlloc_7223_; 
v_reuseFailAlloc_7223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7223_, 0, v___x_7218_);
lean_ctor_set(v_reuseFailAlloc_7223_, 1, v_k_7213_);
lean_ctor_set(v_reuseFailAlloc_7223_, 2, v_v_7214_);
lean_ctor_set(v_reuseFailAlloc_7223_, 3, v_l_7211_);
lean_ctor_set(v_reuseFailAlloc_7223_, 4, v___x_7220_);
v___x_7222_ = v_reuseFailAlloc_7223_;
goto v_reusejp_7221_;
}
v_reusejp_7221_:
{
return v___x_7222_;
}
}
}
}
else
{
lean_object* v_r_7228_; 
v_r_7228_ = lean_ctor_get(v_impl_7124_, 4);
lean_inc(v_r_7228_);
if (lean_obj_tag(v_r_7228_) == 0)
{
lean_object* v_k_7229_; lean_object* v_v_7230_; lean_object* v___x_7232_; uint8_t v_isShared_7233_; uint8_t v_isSharedCheck_7253_; 
v_k_7229_ = lean_ctor_get(v_impl_7124_, 1);
v_v_7230_ = lean_ctor_get(v_impl_7124_, 2);
v_isSharedCheck_7253_ = !lean_is_exclusive(v_impl_7124_);
if (v_isSharedCheck_7253_ == 0)
{
lean_object* v_unused_7254_; lean_object* v_unused_7255_; lean_object* v_unused_7256_; 
v_unused_7254_ = lean_ctor_get(v_impl_7124_, 4);
lean_dec(v_unused_7254_);
v_unused_7255_ = lean_ctor_get(v_impl_7124_, 3);
lean_dec(v_unused_7255_);
v_unused_7256_ = lean_ctor_get(v_impl_7124_, 0);
lean_dec(v_unused_7256_);
v___x_7232_ = v_impl_7124_;
v_isShared_7233_ = v_isSharedCheck_7253_;
goto v_resetjp_7231_;
}
else
{
lean_inc(v_v_7230_);
lean_inc(v_k_7229_);
lean_dec(v_impl_7124_);
v___x_7232_ = lean_box(0);
v_isShared_7233_ = v_isSharedCheck_7253_;
goto v_resetjp_7231_;
}
v_resetjp_7231_:
{
lean_object* v_k_7234_; lean_object* v_v_7235_; lean_object* v___x_7237_; uint8_t v_isShared_7238_; uint8_t v_isSharedCheck_7249_; 
v_k_7234_ = lean_ctor_get(v_r_7228_, 1);
v_v_7235_ = lean_ctor_get(v_r_7228_, 2);
v_isSharedCheck_7249_ = !lean_is_exclusive(v_r_7228_);
if (v_isSharedCheck_7249_ == 0)
{
lean_object* v_unused_7250_; lean_object* v_unused_7251_; lean_object* v_unused_7252_; 
v_unused_7250_ = lean_ctor_get(v_r_7228_, 4);
lean_dec(v_unused_7250_);
v_unused_7251_ = lean_ctor_get(v_r_7228_, 3);
lean_dec(v_unused_7251_);
v_unused_7252_ = lean_ctor_get(v_r_7228_, 0);
lean_dec(v_unused_7252_);
v___x_7237_ = v_r_7228_;
v_isShared_7238_ = v_isSharedCheck_7249_;
goto v_resetjp_7236_;
}
else
{
lean_inc(v_v_7235_);
lean_inc(v_k_7234_);
lean_dec(v_r_7228_);
v___x_7237_ = lean_box(0);
v_isShared_7238_ = v_isSharedCheck_7249_;
goto v_resetjp_7236_;
}
v_resetjp_7236_:
{
lean_object* v___x_7239_; lean_object* v___x_7241_; 
v___x_7239_ = lean_unsigned_to_nat(3u);
if (v_isShared_7238_ == 0)
{
lean_ctor_set(v___x_7237_, 4, v_l_7211_);
lean_ctor_set(v___x_7237_, 3, v_l_7211_);
lean_ctor_set(v___x_7237_, 2, v_v_7230_);
lean_ctor_set(v___x_7237_, 1, v_k_7229_);
lean_ctor_set(v___x_7237_, 0, v___x_7125_);
v___x_7241_ = v___x_7237_;
goto v_reusejp_7240_;
}
else
{
lean_object* v_reuseFailAlloc_7248_; 
v_reuseFailAlloc_7248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7248_, 0, v___x_7125_);
lean_ctor_set(v_reuseFailAlloc_7248_, 1, v_k_7229_);
lean_ctor_set(v_reuseFailAlloc_7248_, 2, v_v_7230_);
lean_ctor_set(v_reuseFailAlloc_7248_, 3, v_l_7211_);
lean_ctor_set(v_reuseFailAlloc_7248_, 4, v_l_7211_);
v___x_7241_ = v_reuseFailAlloc_7248_;
goto v_reusejp_7240_;
}
v_reusejp_7240_:
{
lean_object* v___x_7243_; 
if (v_isShared_7233_ == 0)
{
lean_ctor_set(v___x_7232_, 4, v_l_7211_);
lean_ctor_set(v___x_7232_, 2, v_v_7117_);
lean_ctor_set(v___x_7232_, 1, v_k_7116_);
lean_ctor_set(v___x_7232_, 0, v___x_7125_);
v___x_7243_ = v___x_7232_;
goto v_reusejp_7242_;
}
else
{
lean_object* v_reuseFailAlloc_7247_; 
v_reuseFailAlloc_7247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7247_, 0, v___x_7125_);
lean_ctor_set(v_reuseFailAlloc_7247_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7247_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7247_, 3, v_l_7211_);
lean_ctor_set(v_reuseFailAlloc_7247_, 4, v_l_7211_);
v___x_7243_ = v_reuseFailAlloc_7247_;
goto v_reusejp_7242_;
}
v_reusejp_7242_:
{
lean_object* v___x_7245_; 
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v___x_7243_);
lean_ctor_set(v___x_7121_, 3, v___x_7241_);
lean_ctor_set(v___x_7121_, 2, v_v_7235_);
lean_ctor_set(v___x_7121_, 1, v_k_7234_);
lean_ctor_set(v___x_7121_, 0, v___x_7239_);
v___x_7245_ = v___x_7121_;
goto v_reusejp_7244_;
}
else
{
lean_object* v_reuseFailAlloc_7246_; 
v_reuseFailAlloc_7246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7246_, 0, v___x_7239_);
lean_ctor_set(v_reuseFailAlloc_7246_, 1, v_k_7234_);
lean_ctor_set(v_reuseFailAlloc_7246_, 2, v_v_7235_);
lean_ctor_set(v_reuseFailAlloc_7246_, 3, v___x_7241_);
lean_ctor_set(v_reuseFailAlloc_7246_, 4, v___x_7243_);
v___x_7245_ = v_reuseFailAlloc_7246_;
goto v_reusejp_7244_;
}
v_reusejp_7244_:
{
return v___x_7245_;
}
}
}
}
}
}
else
{
lean_object* v___x_7257_; lean_object* v___x_7259_; 
v___x_7257_ = lean_unsigned_to_nat(2u);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_r_7228_);
lean_ctor_set(v___x_7121_, 3, v_impl_7124_);
lean_ctor_set(v___x_7121_, 0, v___x_7257_);
v___x_7259_ = v___x_7121_;
goto v_reusejp_7258_;
}
else
{
lean_object* v_reuseFailAlloc_7260_; 
v_reuseFailAlloc_7260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7260_, 0, v___x_7257_);
lean_ctor_set(v_reuseFailAlloc_7260_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7260_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7260_, 3, v_impl_7124_);
lean_ctor_set(v_reuseFailAlloc_7260_, 4, v_r_7228_);
v___x_7259_ = v_reuseFailAlloc_7260_;
goto v_reusejp_7258_;
}
v_reusejp_7258_:
{
return v___x_7259_;
}
}
}
}
}
case 1:
{
lean_object* v___x_7262_; 
lean_dec(v_v_7117_);
lean_dec(v_k_7116_);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 2, v_v_7113_);
lean_ctor_set(v___x_7121_, 1, v_k_7112_);
v___x_7262_ = v___x_7121_;
goto v_reusejp_7261_;
}
else
{
lean_object* v_reuseFailAlloc_7263_; 
v_reuseFailAlloc_7263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7263_, 0, v_size_7115_);
lean_ctor_set(v_reuseFailAlloc_7263_, 1, v_k_7112_);
lean_ctor_set(v_reuseFailAlloc_7263_, 2, v_v_7113_);
lean_ctor_set(v_reuseFailAlloc_7263_, 3, v_l_7118_);
lean_ctor_set(v_reuseFailAlloc_7263_, 4, v_r_7119_);
v___x_7262_ = v_reuseFailAlloc_7263_;
goto v_reusejp_7261_;
}
v_reusejp_7261_:
{
return v___x_7262_;
}
}
default: 
{
lean_object* v_impl_7264_; lean_object* v___x_7265_; 
lean_dec(v_size_7115_);
v_impl_7264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7112_, v_v_7113_, v_r_7119_);
v___x_7265_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7118_) == 0)
{
lean_object* v_size_7266_; lean_object* v_size_7267_; lean_object* v_k_7268_; lean_object* v_v_7269_; lean_object* v_l_7270_; lean_object* v_r_7271_; lean_object* v___x_7272_; lean_object* v___x_7273_; uint8_t v___x_7274_; 
v_size_7266_ = lean_ctor_get(v_l_7118_, 0);
v_size_7267_ = lean_ctor_get(v_impl_7264_, 0);
lean_inc(v_size_7267_);
v_k_7268_ = lean_ctor_get(v_impl_7264_, 1);
lean_inc(v_k_7268_);
v_v_7269_ = lean_ctor_get(v_impl_7264_, 2);
lean_inc(v_v_7269_);
v_l_7270_ = lean_ctor_get(v_impl_7264_, 3);
lean_inc(v_l_7270_);
v_r_7271_ = lean_ctor_get(v_impl_7264_, 4);
lean_inc(v_r_7271_);
v___x_7272_ = lean_unsigned_to_nat(3u);
v___x_7273_ = lean_nat_mul(v___x_7272_, v_size_7266_);
v___x_7274_ = lean_nat_dec_lt(v___x_7273_, v_size_7267_);
lean_dec(v___x_7273_);
if (v___x_7274_ == 0)
{
lean_object* v___x_7275_; lean_object* v___x_7276_; lean_object* v___x_7278_; 
lean_dec(v_r_7271_);
lean_dec(v_l_7270_);
lean_dec(v_v_7269_);
lean_dec(v_k_7268_);
v___x_7275_ = lean_nat_add(v___x_7265_, v_size_7266_);
v___x_7276_ = lean_nat_add(v___x_7275_, v_size_7267_);
lean_dec(v_size_7267_);
lean_dec(v___x_7275_);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_impl_7264_);
lean_ctor_set(v___x_7121_, 0, v___x_7276_);
v___x_7278_ = v___x_7121_;
goto v_reusejp_7277_;
}
else
{
lean_object* v_reuseFailAlloc_7279_; 
v_reuseFailAlloc_7279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7279_, 0, v___x_7276_);
lean_ctor_set(v_reuseFailAlloc_7279_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7279_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7279_, 3, v_l_7118_);
lean_ctor_set(v_reuseFailAlloc_7279_, 4, v_impl_7264_);
v___x_7278_ = v_reuseFailAlloc_7279_;
goto v_reusejp_7277_;
}
v_reusejp_7277_:
{
return v___x_7278_;
}
}
else
{
lean_object* v___x_7281_; uint8_t v_isShared_7282_; uint8_t v_isSharedCheck_7343_; 
v_isSharedCheck_7343_ = !lean_is_exclusive(v_impl_7264_);
if (v_isSharedCheck_7343_ == 0)
{
lean_object* v_unused_7344_; lean_object* v_unused_7345_; lean_object* v_unused_7346_; lean_object* v_unused_7347_; lean_object* v_unused_7348_; 
v_unused_7344_ = lean_ctor_get(v_impl_7264_, 4);
lean_dec(v_unused_7344_);
v_unused_7345_ = lean_ctor_get(v_impl_7264_, 3);
lean_dec(v_unused_7345_);
v_unused_7346_ = lean_ctor_get(v_impl_7264_, 2);
lean_dec(v_unused_7346_);
v_unused_7347_ = lean_ctor_get(v_impl_7264_, 1);
lean_dec(v_unused_7347_);
v_unused_7348_ = lean_ctor_get(v_impl_7264_, 0);
lean_dec(v_unused_7348_);
v___x_7281_ = v_impl_7264_;
v_isShared_7282_ = v_isSharedCheck_7343_;
goto v_resetjp_7280_;
}
else
{
lean_dec(v_impl_7264_);
v___x_7281_ = lean_box(0);
v_isShared_7282_ = v_isSharedCheck_7343_;
goto v_resetjp_7280_;
}
v_resetjp_7280_:
{
lean_object* v_size_7283_; lean_object* v_k_7284_; lean_object* v_v_7285_; lean_object* v_l_7286_; lean_object* v_r_7287_; lean_object* v_size_7288_; lean_object* v___x_7289_; lean_object* v___x_7290_; uint8_t v___x_7291_; 
v_size_7283_ = lean_ctor_get(v_l_7270_, 0);
v_k_7284_ = lean_ctor_get(v_l_7270_, 1);
v_v_7285_ = lean_ctor_get(v_l_7270_, 2);
v_l_7286_ = lean_ctor_get(v_l_7270_, 3);
v_r_7287_ = lean_ctor_get(v_l_7270_, 4);
v_size_7288_ = lean_ctor_get(v_r_7271_, 0);
v___x_7289_ = lean_unsigned_to_nat(2u);
v___x_7290_ = lean_nat_mul(v___x_7289_, v_size_7288_);
v___x_7291_ = lean_nat_dec_lt(v_size_7283_, v___x_7290_);
lean_dec(v___x_7290_);
if (v___x_7291_ == 0)
{
lean_object* v___x_7293_; uint8_t v_isShared_7294_; uint8_t v_isSharedCheck_7319_; 
lean_inc(v_r_7287_);
lean_inc(v_l_7286_);
lean_inc(v_v_7285_);
lean_inc(v_k_7284_);
v_isSharedCheck_7319_ = !lean_is_exclusive(v_l_7270_);
if (v_isSharedCheck_7319_ == 0)
{
lean_object* v_unused_7320_; lean_object* v_unused_7321_; lean_object* v_unused_7322_; lean_object* v_unused_7323_; lean_object* v_unused_7324_; 
v_unused_7320_ = lean_ctor_get(v_l_7270_, 4);
lean_dec(v_unused_7320_);
v_unused_7321_ = lean_ctor_get(v_l_7270_, 3);
lean_dec(v_unused_7321_);
v_unused_7322_ = lean_ctor_get(v_l_7270_, 2);
lean_dec(v_unused_7322_);
v_unused_7323_ = lean_ctor_get(v_l_7270_, 1);
lean_dec(v_unused_7323_);
v_unused_7324_ = lean_ctor_get(v_l_7270_, 0);
lean_dec(v_unused_7324_);
v___x_7293_ = v_l_7270_;
v_isShared_7294_ = v_isSharedCheck_7319_;
goto v_resetjp_7292_;
}
else
{
lean_dec(v_l_7270_);
v___x_7293_ = lean_box(0);
v_isShared_7294_ = v_isSharedCheck_7319_;
goto v_resetjp_7292_;
}
v_resetjp_7292_:
{
lean_object* v___x_7295_; lean_object* v___x_7296_; lean_object* v___y_7298_; lean_object* v___y_7299_; lean_object* v___y_7300_; lean_object* v___y_7309_; 
v___x_7295_ = lean_nat_add(v___x_7265_, v_size_7266_);
v___x_7296_ = lean_nat_add(v___x_7295_, v_size_7267_);
lean_dec(v_size_7267_);
if (lean_obj_tag(v_l_7286_) == 0)
{
lean_object* v_size_7317_; 
v_size_7317_ = lean_ctor_get(v_l_7286_, 0);
lean_inc(v_size_7317_);
v___y_7309_ = v_size_7317_;
goto v___jp_7308_;
}
else
{
lean_object* v___x_7318_; 
v___x_7318_ = lean_unsigned_to_nat(0u);
v___y_7309_ = v___x_7318_;
goto v___jp_7308_;
}
v___jp_7297_:
{
lean_object* v___x_7301_; lean_object* v___x_7303_; 
v___x_7301_ = lean_nat_add(v___y_7299_, v___y_7300_);
lean_dec(v___y_7300_);
lean_dec(v___y_7299_);
if (v_isShared_7294_ == 0)
{
lean_ctor_set(v___x_7293_, 4, v_r_7271_);
lean_ctor_set(v___x_7293_, 3, v_r_7287_);
lean_ctor_set(v___x_7293_, 2, v_v_7269_);
lean_ctor_set(v___x_7293_, 1, v_k_7268_);
lean_ctor_set(v___x_7293_, 0, v___x_7301_);
v___x_7303_ = v___x_7293_;
goto v_reusejp_7302_;
}
else
{
lean_object* v_reuseFailAlloc_7307_; 
v_reuseFailAlloc_7307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7307_, 0, v___x_7301_);
lean_ctor_set(v_reuseFailAlloc_7307_, 1, v_k_7268_);
lean_ctor_set(v_reuseFailAlloc_7307_, 2, v_v_7269_);
lean_ctor_set(v_reuseFailAlloc_7307_, 3, v_r_7287_);
lean_ctor_set(v_reuseFailAlloc_7307_, 4, v_r_7271_);
v___x_7303_ = v_reuseFailAlloc_7307_;
goto v_reusejp_7302_;
}
v_reusejp_7302_:
{
lean_object* v___x_7305_; 
if (v_isShared_7282_ == 0)
{
lean_ctor_set(v___x_7281_, 4, v___x_7303_);
lean_ctor_set(v___x_7281_, 3, v___y_7298_);
lean_ctor_set(v___x_7281_, 2, v_v_7285_);
lean_ctor_set(v___x_7281_, 1, v_k_7284_);
lean_ctor_set(v___x_7281_, 0, v___x_7296_);
v___x_7305_ = v___x_7281_;
goto v_reusejp_7304_;
}
else
{
lean_object* v_reuseFailAlloc_7306_; 
v_reuseFailAlloc_7306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7306_, 0, v___x_7296_);
lean_ctor_set(v_reuseFailAlloc_7306_, 1, v_k_7284_);
lean_ctor_set(v_reuseFailAlloc_7306_, 2, v_v_7285_);
lean_ctor_set(v_reuseFailAlloc_7306_, 3, v___y_7298_);
lean_ctor_set(v_reuseFailAlloc_7306_, 4, v___x_7303_);
v___x_7305_ = v_reuseFailAlloc_7306_;
goto v_reusejp_7304_;
}
v_reusejp_7304_:
{
return v___x_7305_;
}
}
}
v___jp_7308_:
{
lean_object* v___x_7310_; lean_object* v___x_7312_; 
v___x_7310_ = lean_nat_add(v___x_7295_, v___y_7309_);
lean_dec(v___y_7309_);
lean_dec(v___x_7295_);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_l_7286_);
lean_ctor_set(v___x_7121_, 0, v___x_7310_);
v___x_7312_ = v___x_7121_;
goto v_reusejp_7311_;
}
else
{
lean_object* v_reuseFailAlloc_7316_; 
v_reuseFailAlloc_7316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7316_, 0, v___x_7310_);
lean_ctor_set(v_reuseFailAlloc_7316_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7316_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7316_, 3, v_l_7118_);
lean_ctor_set(v_reuseFailAlloc_7316_, 4, v_l_7286_);
v___x_7312_ = v_reuseFailAlloc_7316_;
goto v_reusejp_7311_;
}
v_reusejp_7311_:
{
lean_object* v___x_7313_; 
v___x_7313_ = lean_nat_add(v___x_7265_, v_size_7288_);
if (lean_obj_tag(v_r_7287_) == 0)
{
lean_object* v_size_7314_; 
v_size_7314_ = lean_ctor_get(v_r_7287_, 0);
lean_inc(v_size_7314_);
v___y_7298_ = v___x_7312_;
v___y_7299_ = v___x_7313_;
v___y_7300_ = v_size_7314_;
goto v___jp_7297_;
}
else
{
lean_object* v___x_7315_; 
v___x_7315_ = lean_unsigned_to_nat(0u);
v___y_7298_ = v___x_7312_;
v___y_7299_ = v___x_7313_;
v___y_7300_ = v___x_7315_;
goto v___jp_7297_;
}
}
}
}
}
else
{
lean_object* v___x_7325_; lean_object* v___x_7326_; lean_object* v___x_7327_; lean_object* v___x_7329_; 
lean_del_object(v___x_7121_);
v___x_7325_ = lean_nat_add(v___x_7265_, v_size_7266_);
v___x_7326_ = lean_nat_add(v___x_7325_, v_size_7267_);
lean_dec(v_size_7267_);
v___x_7327_ = lean_nat_add(v___x_7325_, v_size_7283_);
lean_dec(v___x_7325_);
lean_inc_ref(v_l_7118_);
if (v_isShared_7282_ == 0)
{
lean_ctor_set(v___x_7281_, 4, v_l_7270_);
lean_ctor_set(v___x_7281_, 3, v_l_7118_);
lean_ctor_set(v___x_7281_, 2, v_v_7117_);
lean_ctor_set(v___x_7281_, 1, v_k_7116_);
lean_ctor_set(v___x_7281_, 0, v___x_7327_);
v___x_7329_ = v___x_7281_;
goto v_reusejp_7328_;
}
else
{
lean_object* v_reuseFailAlloc_7342_; 
v_reuseFailAlloc_7342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7342_, 0, v___x_7327_);
lean_ctor_set(v_reuseFailAlloc_7342_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7342_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7342_, 3, v_l_7118_);
lean_ctor_set(v_reuseFailAlloc_7342_, 4, v_l_7270_);
v___x_7329_ = v_reuseFailAlloc_7342_;
goto v_reusejp_7328_;
}
v_reusejp_7328_:
{
lean_object* v___x_7331_; uint8_t v_isShared_7332_; uint8_t v_isSharedCheck_7336_; 
v_isSharedCheck_7336_ = !lean_is_exclusive(v_l_7118_);
if (v_isSharedCheck_7336_ == 0)
{
lean_object* v_unused_7337_; lean_object* v_unused_7338_; lean_object* v_unused_7339_; lean_object* v_unused_7340_; lean_object* v_unused_7341_; 
v_unused_7337_ = lean_ctor_get(v_l_7118_, 4);
lean_dec(v_unused_7337_);
v_unused_7338_ = lean_ctor_get(v_l_7118_, 3);
lean_dec(v_unused_7338_);
v_unused_7339_ = lean_ctor_get(v_l_7118_, 2);
lean_dec(v_unused_7339_);
v_unused_7340_ = lean_ctor_get(v_l_7118_, 1);
lean_dec(v_unused_7340_);
v_unused_7341_ = lean_ctor_get(v_l_7118_, 0);
lean_dec(v_unused_7341_);
v___x_7331_ = v_l_7118_;
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
else
{
lean_dec(v_l_7118_);
v___x_7331_ = lean_box(0);
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
v_resetjp_7330_:
{
lean_object* v___x_7334_; 
if (v_isShared_7332_ == 0)
{
lean_ctor_set(v___x_7331_, 4, v_r_7271_);
lean_ctor_set(v___x_7331_, 3, v___x_7329_);
lean_ctor_set(v___x_7331_, 2, v_v_7269_);
lean_ctor_set(v___x_7331_, 1, v_k_7268_);
lean_ctor_set(v___x_7331_, 0, v___x_7326_);
v___x_7334_ = v___x_7331_;
goto v_reusejp_7333_;
}
else
{
lean_object* v_reuseFailAlloc_7335_; 
v_reuseFailAlloc_7335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7335_, 0, v___x_7326_);
lean_ctor_set(v_reuseFailAlloc_7335_, 1, v_k_7268_);
lean_ctor_set(v_reuseFailAlloc_7335_, 2, v_v_7269_);
lean_ctor_set(v_reuseFailAlloc_7335_, 3, v___x_7329_);
lean_ctor_set(v_reuseFailAlloc_7335_, 4, v_r_7271_);
v___x_7334_ = v_reuseFailAlloc_7335_;
goto v_reusejp_7333_;
}
v_reusejp_7333_:
{
return v___x_7334_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7349_; 
v_l_7349_ = lean_ctor_get(v_impl_7264_, 3);
lean_inc(v_l_7349_);
if (lean_obj_tag(v_l_7349_) == 0)
{
lean_object* v_r_7350_; lean_object* v_k_7351_; lean_object* v_v_7352_; lean_object* v___x_7354_; uint8_t v_isShared_7355_; uint8_t v_isSharedCheck_7375_; 
v_r_7350_ = lean_ctor_get(v_impl_7264_, 4);
v_k_7351_ = lean_ctor_get(v_impl_7264_, 1);
v_v_7352_ = lean_ctor_get(v_impl_7264_, 2);
v_isSharedCheck_7375_ = !lean_is_exclusive(v_impl_7264_);
if (v_isSharedCheck_7375_ == 0)
{
lean_object* v_unused_7376_; lean_object* v_unused_7377_; 
v_unused_7376_ = lean_ctor_get(v_impl_7264_, 3);
lean_dec(v_unused_7376_);
v_unused_7377_ = lean_ctor_get(v_impl_7264_, 0);
lean_dec(v_unused_7377_);
v___x_7354_ = v_impl_7264_;
v_isShared_7355_ = v_isSharedCheck_7375_;
goto v_resetjp_7353_;
}
else
{
lean_inc(v_r_7350_);
lean_inc(v_v_7352_);
lean_inc(v_k_7351_);
lean_dec(v_impl_7264_);
v___x_7354_ = lean_box(0);
v_isShared_7355_ = v_isSharedCheck_7375_;
goto v_resetjp_7353_;
}
v_resetjp_7353_:
{
lean_object* v_k_7356_; lean_object* v_v_7357_; lean_object* v___x_7359_; uint8_t v_isShared_7360_; uint8_t v_isSharedCheck_7371_; 
v_k_7356_ = lean_ctor_get(v_l_7349_, 1);
v_v_7357_ = lean_ctor_get(v_l_7349_, 2);
v_isSharedCheck_7371_ = !lean_is_exclusive(v_l_7349_);
if (v_isSharedCheck_7371_ == 0)
{
lean_object* v_unused_7372_; lean_object* v_unused_7373_; lean_object* v_unused_7374_; 
v_unused_7372_ = lean_ctor_get(v_l_7349_, 4);
lean_dec(v_unused_7372_);
v_unused_7373_ = lean_ctor_get(v_l_7349_, 3);
lean_dec(v_unused_7373_);
v_unused_7374_ = lean_ctor_get(v_l_7349_, 0);
lean_dec(v_unused_7374_);
v___x_7359_ = v_l_7349_;
v_isShared_7360_ = v_isSharedCheck_7371_;
goto v_resetjp_7358_;
}
else
{
lean_inc(v_v_7357_);
lean_inc(v_k_7356_);
lean_dec(v_l_7349_);
v___x_7359_ = lean_box(0);
v_isShared_7360_ = v_isSharedCheck_7371_;
goto v_resetjp_7358_;
}
v_resetjp_7358_:
{
lean_object* v___x_7361_; lean_object* v___x_7363_; 
v___x_7361_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7350_, 2);
if (v_isShared_7360_ == 0)
{
lean_ctor_set(v___x_7359_, 4, v_r_7350_);
lean_ctor_set(v___x_7359_, 3, v_r_7350_);
lean_ctor_set(v___x_7359_, 2, v_v_7117_);
lean_ctor_set(v___x_7359_, 1, v_k_7116_);
lean_ctor_set(v___x_7359_, 0, v___x_7265_);
v___x_7363_ = v___x_7359_;
goto v_reusejp_7362_;
}
else
{
lean_object* v_reuseFailAlloc_7370_; 
v_reuseFailAlloc_7370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7370_, 0, v___x_7265_);
lean_ctor_set(v_reuseFailAlloc_7370_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7370_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7370_, 3, v_r_7350_);
lean_ctor_set(v_reuseFailAlloc_7370_, 4, v_r_7350_);
v___x_7363_ = v_reuseFailAlloc_7370_;
goto v_reusejp_7362_;
}
v_reusejp_7362_:
{
lean_object* v___x_7365_; 
lean_inc(v_r_7350_);
if (v_isShared_7355_ == 0)
{
lean_ctor_set(v___x_7354_, 3, v_r_7350_);
lean_ctor_set(v___x_7354_, 0, v___x_7265_);
v___x_7365_ = v___x_7354_;
goto v_reusejp_7364_;
}
else
{
lean_object* v_reuseFailAlloc_7369_; 
v_reuseFailAlloc_7369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7369_, 0, v___x_7265_);
lean_ctor_set(v_reuseFailAlloc_7369_, 1, v_k_7351_);
lean_ctor_set(v_reuseFailAlloc_7369_, 2, v_v_7352_);
lean_ctor_set(v_reuseFailAlloc_7369_, 3, v_r_7350_);
lean_ctor_set(v_reuseFailAlloc_7369_, 4, v_r_7350_);
v___x_7365_ = v_reuseFailAlloc_7369_;
goto v_reusejp_7364_;
}
v_reusejp_7364_:
{
lean_object* v___x_7367_; 
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v___x_7365_);
lean_ctor_set(v___x_7121_, 3, v___x_7363_);
lean_ctor_set(v___x_7121_, 2, v_v_7357_);
lean_ctor_set(v___x_7121_, 1, v_k_7356_);
lean_ctor_set(v___x_7121_, 0, v___x_7361_);
v___x_7367_ = v___x_7121_;
goto v_reusejp_7366_;
}
else
{
lean_object* v_reuseFailAlloc_7368_; 
v_reuseFailAlloc_7368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7368_, 0, v___x_7361_);
lean_ctor_set(v_reuseFailAlloc_7368_, 1, v_k_7356_);
lean_ctor_set(v_reuseFailAlloc_7368_, 2, v_v_7357_);
lean_ctor_set(v_reuseFailAlloc_7368_, 3, v___x_7363_);
lean_ctor_set(v_reuseFailAlloc_7368_, 4, v___x_7365_);
v___x_7367_ = v_reuseFailAlloc_7368_;
goto v_reusejp_7366_;
}
v_reusejp_7366_:
{
return v___x_7367_;
}
}
}
}
}
}
else
{
lean_object* v_r_7378_; 
v_r_7378_ = lean_ctor_get(v_impl_7264_, 4);
lean_inc(v_r_7378_);
if (lean_obj_tag(v_r_7378_) == 0)
{
lean_object* v_k_7379_; lean_object* v_v_7380_; lean_object* v___x_7382_; uint8_t v_isShared_7383_; uint8_t v_isSharedCheck_7391_; 
v_k_7379_ = lean_ctor_get(v_impl_7264_, 1);
v_v_7380_ = lean_ctor_get(v_impl_7264_, 2);
v_isSharedCheck_7391_ = !lean_is_exclusive(v_impl_7264_);
if (v_isSharedCheck_7391_ == 0)
{
lean_object* v_unused_7392_; lean_object* v_unused_7393_; lean_object* v_unused_7394_; 
v_unused_7392_ = lean_ctor_get(v_impl_7264_, 4);
lean_dec(v_unused_7392_);
v_unused_7393_ = lean_ctor_get(v_impl_7264_, 3);
lean_dec(v_unused_7393_);
v_unused_7394_ = lean_ctor_get(v_impl_7264_, 0);
lean_dec(v_unused_7394_);
v___x_7382_ = v_impl_7264_;
v_isShared_7383_ = v_isSharedCheck_7391_;
goto v_resetjp_7381_;
}
else
{
lean_inc(v_v_7380_);
lean_inc(v_k_7379_);
lean_dec(v_impl_7264_);
v___x_7382_ = lean_box(0);
v_isShared_7383_ = v_isSharedCheck_7391_;
goto v_resetjp_7381_;
}
v_resetjp_7381_:
{
lean_object* v___x_7384_; lean_object* v___x_7386_; 
v___x_7384_ = lean_unsigned_to_nat(3u);
if (v_isShared_7383_ == 0)
{
lean_ctor_set(v___x_7382_, 4, v_l_7349_);
lean_ctor_set(v___x_7382_, 2, v_v_7117_);
lean_ctor_set(v___x_7382_, 1, v_k_7116_);
lean_ctor_set(v___x_7382_, 0, v___x_7265_);
v___x_7386_ = v___x_7382_;
goto v_reusejp_7385_;
}
else
{
lean_object* v_reuseFailAlloc_7390_; 
v_reuseFailAlloc_7390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7390_, 0, v___x_7265_);
lean_ctor_set(v_reuseFailAlloc_7390_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7390_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7390_, 3, v_l_7349_);
lean_ctor_set(v_reuseFailAlloc_7390_, 4, v_l_7349_);
v___x_7386_ = v_reuseFailAlloc_7390_;
goto v_reusejp_7385_;
}
v_reusejp_7385_:
{
lean_object* v___x_7388_; 
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_r_7378_);
lean_ctor_set(v___x_7121_, 3, v___x_7386_);
lean_ctor_set(v___x_7121_, 2, v_v_7380_);
lean_ctor_set(v___x_7121_, 1, v_k_7379_);
lean_ctor_set(v___x_7121_, 0, v___x_7384_);
v___x_7388_ = v___x_7121_;
goto v_reusejp_7387_;
}
else
{
lean_object* v_reuseFailAlloc_7389_; 
v_reuseFailAlloc_7389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7389_, 0, v___x_7384_);
lean_ctor_set(v_reuseFailAlloc_7389_, 1, v_k_7379_);
lean_ctor_set(v_reuseFailAlloc_7389_, 2, v_v_7380_);
lean_ctor_set(v_reuseFailAlloc_7389_, 3, v___x_7386_);
lean_ctor_set(v_reuseFailAlloc_7389_, 4, v_r_7378_);
v___x_7388_ = v_reuseFailAlloc_7389_;
goto v_reusejp_7387_;
}
v_reusejp_7387_:
{
return v___x_7388_;
}
}
}
}
else
{
lean_object* v___x_7395_; lean_object* v___x_7397_; 
v___x_7395_ = lean_unsigned_to_nat(2u);
if (v_isShared_7122_ == 0)
{
lean_ctor_set(v___x_7121_, 4, v_impl_7264_);
lean_ctor_set(v___x_7121_, 3, v_r_7378_);
lean_ctor_set(v___x_7121_, 0, v___x_7395_);
v___x_7397_ = v___x_7121_;
goto v_reusejp_7396_;
}
else
{
lean_object* v_reuseFailAlloc_7398_; 
v_reuseFailAlloc_7398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7398_, 0, v___x_7395_);
lean_ctor_set(v_reuseFailAlloc_7398_, 1, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7398_, 2, v_v_7117_);
lean_ctor_set(v_reuseFailAlloc_7398_, 3, v_r_7378_);
lean_ctor_set(v_reuseFailAlloc_7398_, 4, v_impl_7264_);
v___x_7397_ = v_reuseFailAlloc_7398_;
goto v_reusejp_7396_;
}
v_reusejp_7396_:
{
return v___x_7397_;
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
lean_object* v___x_7400_; lean_object* v___x_7401_; 
v___x_7400_ = lean_unsigned_to_nat(1u);
v___x_7401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7401_, 0, v___x_7400_);
lean_ctor_set(v___x_7401_, 1, v_k_7112_);
lean_ctor_set(v___x_7401_, 2, v_v_7113_);
lean_ctor_set(v___x_7401_, 3, v_t_7114_);
lean_ctor_set(v___x_7401_, 4, v_t_7114_);
return v___x_7401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7402_, lean_object* v_ps_7403_, lean_object* v_v_7404_, lean_object* v_o_7405_){
_start:
{
lean_object* v_name_7406_; lean_object* v_deps_7407_; lean_object* v_o_7408_; uint8_t v___x_7409_; 
v_name_7406_ = lean_ctor_get(v_lib_7402_, 1);
lean_inc_ref(v_name_7406_);
v_deps_7407_ = lean_ctor_get(v_lib_7402_, 2);
lean_inc_ref(v_deps_7407_);
v_o_7408_ = lean_array_push(v_o_7405_, v_lib_7402_);
v___x_7409_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7406_, v_v_7404_);
if (v___x_7409_ == 0)
{
uint8_t v___x_7410_; 
v___x_7410_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7406_, v_ps_7403_);
if (v___x_7410_ == 0)
{
lean_object* v_ps_7411_; lean_object* v___y_7413_; 
lean_inc_ref(v_name_7406_);
v_ps_7411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7411_, 0, v_name_7406_);
lean_ctor_set(v_ps_7411_, 1, v_ps_7403_);
if (v___x_7409_ == 0)
{
lean_object* v___x_7427_; lean_object* v___x_7428_; 
v___x_7427_ = lean_box(0);
v___x_7428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7406_, v___x_7427_, v_v_7404_);
v___y_7413_ = v___x_7428_;
goto v___jp_7412_;
}
else
{
lean_dec_ref(v_name_7406_);
v___y_7413_ = v_v_7404_;
goto v___jp_7412_;
}
v___jp_7412_:
{
lean_object* v___x_7414_; lean_object* v___x_7415_; lean_object* v___x_7416_; uint8_t v___x_7417_; 
v___x_7414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7414_, 0, v___y_7413_);
lean_ctor_set(v___x_7414_, 1, v_o_7408_);
v___x_7415_ = lean_unsigned_to_nat(0u);
v___x_7416_ = lean_array_get_size(v_deps_7407_);
v___x_7417_ = lean_nat_dec_lt(v___x_7415_, v___x_7416_);
if (v___x_7417_ == 0)
{
lean_object* v___x_7418_; 
lean_dec_ref_known(v_ps_7411_, 2);
lean_dec_ref(v_deps_7407_);
v___x_7418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7418_, 0, v___x_7414_);
return v___x_7418_;
}
else
{
uint8_t v___x_7419_; 
v___x_7419_ = lean_nat_dec_le(v___x_7416_, v___x_7416_);
if (v___x_7419_ == 0)
{
if (v___x_7417_ == 0)
{
lean_object* v___x_7420_; 
lean_dec_ref_known(v_ps_7411_, 2);
lean_dec_ref(v_deps_7407_);
v___x_7420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7420_, 0, v___x_7414_);
return v___x_7420_;
}
else
{
size_t v___x_7421_; size_t v___x_7422_; lean_object* v___x_7423_; 
v___x_7421_ = ((size_t)0ULL);
v___x_7422_ = lean_usize_of_nat(v___x_7416_);
v___x_7423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7411_, v_deps_7407_, v___x_7421_, v___x_7422_, v___x_7414_);
lean_dec_ref(v_deps_7407_);
return v___x_7423_;
}
}
else
{
size_t v___x_7424_; size_t v___x_7425_; lean_object* v___x_7426_; 
v___x_7424_ = ((size_t)0ULL);
v___x_7425_ = lean_usize_of_nat(v___x_7416_);
v___x_7426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7411_, v_deps_7407_, v___x_7424_, v___x_7425_, v___x_7414_);
lean_dec_ref(v_deps_7407_);
return v___x_7426_;
}
}
}
}
else
{
lean_object* v___x_7429_; lean_object* v___x_7430_; 
lean_dec_ref(v_o_7408_);
lean_dec_ref(v_deps_7407_);
lean_dec(v_v_7404_);
v___x_7429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7429_, 0, v_name_7406_);
lean_ctor_set(v___x_7429_, 1, v_ps_7403_);
v___x_7430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7430_, 0, v___x_7429_);
return v___x_7430_;
}
}
else
{
lean_object* v___x_7431_; lean_object* v___x_7432_; 
lean_dec_ref(v_deps_7407_);
lean_dec_ref(v_name_7406_);
lean_dec(v_ps_7403_);
v___x_7431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7431_, 0, v_v_7404_);
lean_ctor_set(v___x_7431_, 1, v_o_7408_);
v___x_7432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7432_, 0, v___x_7431_);
return v___x_7432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7433_, lean_object* v_as_7434_, size_t v_i_7435_, size_t v_stop_7436_, lean_object* v_b_7437_){
_start:
{
uint8_t v___x_7438_; 
v___x_7438_ = lean_usize_dec_eq(v_i_7435_, v_stop_7436_);
if (v___x_7438_ == 0)
{
lean_object* v_fst_7439_; lean_object* v_snd_7440_; lean_object* v___x_7441_; lean_object* v___x_7442_; 
v_fst_7439_ = lean_ctor_get(v_b_7437_, 0);
lean_inc(v_fst_7439_);
v_snd_7440_ = lean_ctor_get(v_b_7437_, 1);
lean_inc(v_snd_7440_);
lean_dec_ref(v_b_7437_);
v___x_7441_ = lean_array_uget_borrowed(v_as_7434_, v_i_7435_);
lean_inc(v_ps_7433_);
lean_inc(v___x_7441_);
v___x_7442_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7441_, v_ps_7433_, v_fst_7439_, v_snd_7440_);
if (lean_obj_tag(v___x_7442_) == 0)
{
lean_dec(v_ps_7433_);
return v___x_7442_;
}
else
{
lean_object* v_a_7443_; size_t v___x_7444_; size_t v___x_7445_; 
v_a_7443_ = lean_ctor_get(v___x_7442_, 0);
lean_inc(v_a_7443_);
lean_dec_ref_known(v___x_7442_, 1);
v___x_7444_ = ((size_t)1ULL);
v___x_7445_ = lean_usize_add(v_i_7435_, v___x_7444_);
v_i_7435_ = v___x_7445_;
v_b_7437_ = v_a_7443_;
goto _start;
}
}
else
{
lean_object* v___x_7447_; 
lean_dec(v_ps_7433_);
v___x_7447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7447_, 0, v_b_7437_);
return v___x_7447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7448_, lean_object* v_as_7449_, lean_object* v_i_7450_, lean_object* v_stop_7451_, lean_object* v_b_7452_){
_start:
{
size_t v_i_boxed_7453_; size_t v_stop_boxed_7454_; lean_object* v_res_7455_; 
v_i_boxed_7453_ = lean_unbox_usize(v_i_7450_);
lean_dec(v_i_7450_);
v_stop_boxed_7454_ = lean_unbox_usize(v_stop_7451_);
lean_dec(v_stop_7451_);
v_res_7455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7448_, v_as_7449_, v_i_boxed_7453_, v_stop_boxed_7454_, v_b_7452_);
lean_dec_ref(v_as_7449_);
return v_res_7455_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7456_, lean_object* v_k_7457_, lean_object* v_t_7458_){
_start:
{
uint8_t v___x_7459_; 
v___x_7459_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7457_, v_t_7458_);
return v___x_7459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7460_, lean_object* v_k_7461_, lean_object* v_t_7462_){
_start:
{
uint8_t v_res_7463_; lean_object* v_r_7464_; 
v_res_7463_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7460_, v_k_7461_, v_t_7462_);
lean_dec(v_t_7462_);
lean_dec_ref(v_k_7461_);
v_r_7464_ = lean_box(v_res_7463_);
return v_r_7464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7465_, lean_object* v_k_7466_, lean_object* v_v_7467_, lean_object* v_t_7468_, lean_object* v_hl_7469_){
_start:
{
lean_object* v___x_7470_; 
v___x_7470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7466_, v_v_7467_, v_t_7468_);
return v___x_7470_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7472_, lean_object* v_a_7473_){
_start:
{
if (lean_obj_tag(v_a_7472_) == 0)
{
lean_object* v___x_7474_; 
v___x_7474_ = l_List_reverse___redArg(v_a_7473_);
return v___x_7474_;
}
else
{
lean_object* v_head_7475_; lean_object* v_tail_7476_; lean_object* v___x_7478_; uint8_t v_isShared_7479_; uint8_t v_isSharedCheck_7486_; 
v_head_7475_ = lean_ctor_get(v_a_7472_, 0);
v_tail_7476_ = lean_ctor_get(v_a_7472_, 1);
v_isSharedCheck_7486_ = !lean_is_exclusive(v_a_7472_);
if (v_isSharedCheck_7486_ == 0)
{
v___x_7478_ = v_a_7472_;
v_isShared_7479_ = v_isSharedCheck_7486_;
goto v_resetjp_7477_;
}
else
{
lean_inc(v_tail_7476_);
lean_inc(v_head_7475_);
lean_dec(v_a_7472_);
v___x_7478_ = lean_box(0);
v_isShared_7479_ = v_isSharedCheck_7486_;
goto v_resetjp_7477_;
}
v_resetjp_7477_:
{
lean_object* v___x_7480_; lean_object* v___x_7481_; lean_object* v___x_7483_; 
v___x_7480_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7481_ = lean_string_append(v___x_7480_, v_head_7475_);
lean_dec(v_head_7475_);
if (v_isShared_7479_ == 0)
{
lean_ctor_set(v___x_7478_, 1, v_a_7473_);
lean_ctor_set(v___x_7478_, 0, v___x_7481_);
v___x_7483_ = v___x_7478_;
goto v_reusejp_7482_;
}
else
{
lean_object* v_reuseFailAlloc_7485_; 
v_reuseFailAlloc_7485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7485_, 0, v___x_7481_);
lean_ctor_set(v_reuseFailAlloc_7485_, 1, v_a_7473_);
v___x_7483_ = v_reuseFailAlloc_7485_;
goto v_reusejp_7482_;
}
v_reusejp_7482_:
{
v_a_7472_ = v_tail_7476_;
v_a_7473_ = v___x_7483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7487_){
_start:
{
lean_object* v___x_7488_; lean_object* v___x_7489_; lean_object* v___x_7490_; lean_object* v___x_7491_; 
v___x_7488_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7489_ = lean_box(0);
v___x_7490_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7487_, v___x_7489_);
v___x_7491_ = l_String_intercalate(v___x_7488_, v___x_7490_);
return v___x_7491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7492_, size_t v_i_7493_, size_t v_stop_7494_, lean_object* v_b_7495_){
_start:
{
uint8_t v___x_7496_; 
v___x_7496_ = lean_usize_dec_eq(v_i_7493_, v_stop_7494_);
if (v___x_7496_ == 0)
{
lean_object* v_fst_7497_; lean_object* v_snd_7498_; lean_object* v___x_7499_; lean_object* v___x_7500_; lean_object* v___x_7501_; 
v_fst_7497_ = lean_ctor_get(v_b_7495_, 0);
lean_inc(v_fst_7497_);
v_snd_7498_ = lean_ctor_get(v_b_7495_, 1);
lean_inc(v_snd_7498_);
lean_dec_ref(v_b_7495_);
v___x_7499_ = lean_array_uget_borrowed(v_as_7492_, v_i_7493_);
v___x_7500_ = lean_box(0);
lean_inc(v___x_7499_);
v___x_7501_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7499_, v___x_7500_, v_fst_7497_, v_snd_7498_);
if (lean_obj_tag(v___x_7501_) == 0)
{
return v___x_7501_;
}
else
{
lean_object* v_a_7502_; size_t v___x_7503_; size_t v___x_7504_; 
v_a_7502_ = lean_ctor_get(v___x_7501_, 0);
lean_inc(v_a_7502_);
lean_dec_ref_known(v___x_7501_, 1);
v___x_7503_ = ((size_t)1ULL);
v___x_7504_ = lean_usize_add(v_i_7493_, v___x_7503_);
v_i_7493_ = v___x_7504_;
v_b_7495_ = v_a_7502_;
goto _start;
}
}
else
{
lean_object* v___x_7506_; 
v___x_7506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7506_, 0, v_b_7495_);
return v___x_7506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7507_, lean_object* v_i_7508_, lean_object* v_stop_7509_, lean_object* v_b_7510_){
_start:
{
size_t v_i_boxed_7511_; size_t v_stop_boxed_7512_; lean_object* v_res_7513_; 
v_i_boxed_7511_ = lean_unbox_usize(v_i_7508_);
lean_dec(v_i_7508_);
v_stop_boxed_7512_ = lean_unbox_usize(v_stop_7509_);
lean_dec(v_stop_7509_);
v_res_7513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7507_, v_i_boxed_7511_, v_stop_boxed_7512_, v_b_7510_);
lean_dec_ref(v_as_7507_);
return v_res_7513_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7520_, lean_object* v_a_7521_){
_start:
{
lean_object* v_snd_7524_; lean_object* v___y_7527_; lean_object* v___x_7551_; lean_object* v___x_7552_; lean_object* v___x_7553_; uint8_t v___x_7554_; 
v___x_7551_ = lean_unsigned_to_nat(0u);
v___x_7552_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7553_ = lean_array_get_size(v_libs_7520_);
v___x_7554_ = lean_nat_dec_lt(v___x_7551_, v___x_7553_);
if (v___x_7554_ == 0)
{
v_snd_7524_ = v___x_7552_;
goto v___jp_7523_;
}
else
{
lean_object* v___x_7555_; uint8_t v___x_7556_; 
v___x_7555_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7556_ = lean_nat_dec_le(v___x_7553_, v___x_7553_);
if (v___x_7556_ == 0)
{
if (v___x_7554_ == 0)
{
v_snd_7524_ = v___x_7552_;
goto v___jp_7523_;
}
else
{
size_t v___x_7557_; size_t v___x_7558_; lean_object* v___x_7559_; 
v___x_7557_ = ((size_t)0ULL);
v___x_7558_ = lean_usize_of_nat(v___x_7553_);
v___x_7559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7520_, v___x_7557_, v___x_7558_, v___x_7555_);
v___y_7527_ = v___x_7559_;
goto v___jp_7526_;
}
}
else
{
size_t v___x_7560_; size_t v___x_7561_; lean_object* v___x_7562_; 
v___x_7560_ = ((size_t)0ULL);
v___x_7561_ = lean_usize_of_nat(v___x_7553_);
v___x_7562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7520_, v___x_7560_, v___x_7561_, v___x_7555_);
v___y_7527_ = v___x_7562_;
goto v___jp_7526_;
}
}
v___jp_7523_:
{
lean_object* v___x_7525_; 
v___x_7525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7525_, 0, v_snd_7524_);
lean_ctor_set(v___x_7525_, 1, v_a_7521_);
return v___x_7525_;
}
v___jp_7526_:
{
if (lean_obj_tag(v___y_7527_) == 0)
{
lean_object* v_a_7528_; lean_object* v_log_7529_; uint8_t v_action_7530_; uint8_t v_wantsRebuild_7531_; lean_object* v_trace_7532_; lean_object* v_buildTime_7533_; lean_object* v___x_7535_; uint8_t v_isShared_7536_; uint8_t v_isSharedCheck_7548_; 
v_a_7528_ = lean_ctor_get(v___y_7527_, 0);
lean_inc(v_a_7528_);
lean_dec_ref_known(v___y_7527_, 1);
v_log_7529_ = lean_ctor_get(v_a_7521_, 0);
v_action_7530_ = lean_ctor_get_uint8(v_a_7521_, sizeof(void*)*3);
v_wantsRebuild_7531_ = lean_ctor_get_uint8(v_a_7521_, sizeof(void*)*3 + 1);
v_trace_7532_ = lean_ctor_get(v_a_7521_, 1);
v_buildTime_7533_ = lean_ctor_get(v_a_7521_, 2);
v_isSharedCheck_7548_ = !lean_is_exclusive(v_a_7521_);
if (v_isSharedCheck_7548_ == 0)
{
v___x_7535_ = v_a_7521_;
v_isShared_7536_ = v_isSharedCheck_7548_;
goto v_resetjp_7534_;
}
else
{
lean_inc(v_buildTime_7533_);
lean_inc(v_trace_7532_);
lean_inc(v_log_7529_);
lean_dec(v_a_7521_);
v___x_7535_ = lean_box(0);
v_isShared_7536_ = v_isSharedCheck_7548_;
goto v_resetjp_7534_;
}
v_resetjp_7534_:
{
lean_object* v___x_7537_; lean_object* v___x_7538_; lean_object* v___x_7539_; uint8_t v___x_7540_; lean_object* v___x_7541_; lean_object* v___x_7542_; lean_object* v___x_7543_; lean_object* v___x_7545_; 
v___x_7537_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7538_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7528_);
v___x_7539_ = lean_string_append(v___x_7537_, v___x_7538_);
lean_dec_ref(v___x_7538_);
v___x_7540_ = 3;
v___x_7541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7541_, 0, v___x_7539_);
lean_ctor_set_uint8(v___x_7541_, sizeof(void*)*1, v___x_7540_);
v___x_7542_ = lean_array_get_size(v_log_7529_);
v___x_7543_ = lean_array_push(v_log_7529_, v___x_7541_);
if (v_isShared_7536_ == 0)
{
lean_ctor_set(v___x_7535_, 0, v___x_7543_);
v___x_7545_ = v___x_7535_;
goto v_reusejp_7544_;
}
else
{
lean_object* v_reuseFailAlloc_7547_; 
v_reuseFailAlloc_7547_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7547_, 0, v___x_7543_);
lean_ctor_set(v_reuseFailAlloc_7547_, 1, v_trace_7532_);
lean_ctor_set(v_reuseFailAlloc_7547_, 2, v_buildTime_7533_);
lean_ctor_set_uint8(v_reuseFailAlloc_7547_, sizeof(void*)*3, v_action_7530_);
lean_ctor_set_uint8(v_reuseFailAlloc_7547_, sizeof(void*)*3 + 1, v_wantsRebuild_7531_);
v___x_7545_ = v_reuseFailAlloc_7547_;
goto v_reusejp_7544_;
}
v_reusejp_7544_:
{
lean_object* v___x_7546_; 
v___x_7546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7546_, 0, v___x_7542_);
lean_ctor_set(v___x_7546_, 1, v___x_7545_);
return v___x_7546_;
}
}
}
else
{
lean_object* v_a_7549_; lean_object* v_snd_7550_; 
v_a_7549_ = lean_ctor_get(v___y_7527_, 0);
lean_inc(v_a_7549_);
lean_dec_ref_known(v___y_7527_, 1);
v_snd_7550_ = lean_ctor_get(v_a_7549_, 1);
lean_inc(v_snd_7550_);
lean_dec(v_a_7549_);
v_snd_7524_ = v_snd_7550_;
goto v___jp_7523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7563_, lean_object* v_a_7564_, lean_object* v_a_7565_){
_start:
{
lean_object* v_res_7566_; 
v_res_7566_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7563_, v_a_7564_);
lean_dec_ref(v_libs_7563_);
return v_res_7566_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7567_, lean_object* v_a_7568_, lean_object* v_a_7569_, lean_object* v_a_7570_, lean_object* v_a_7571_, lean_object* v_a_7572_, lean_object* v_a_7573_){
_start:
{
lean_object* v___x_7575_; 
v___x_7575_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7567_, v_a_7573_);
return v___x_7575_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_){
_start:
{
lean_object* v_res_7584_; 
v_res_7584_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7576_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_, v_a_7581_, v_a_7582_);
lean_dec_ref(v_a_7581_);
lean_dec(v_a_7580_);
lean_dec(v_a_7579_);
lean_dec(v_a_7578_);
lean_dec_ref(v_a_7577_);
lean_dec_ref(v_libs_7576_);
return v_res_7584_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7585_, lean_object* v_weakArgs_7586_, lean_object* v_traceArgs_7587_, lean_object* v_libFile_7588_, lean_object* v_linker_7589_, lean_object* v_libs_7590_, lean_object* v___y_7591_, lean_object* v___y_7592_, lean_object* v___y_7593_, lean_object* v___y_7594_, lean_object* v___y_7595_, lean_object* v___y_7596_){
_start:
{
lean_object* v_log_7598_; uint8_t v_action_7599_; uint8_t v_wantsRebuild_7600_; lean_object* v_trace_7601_; lean_object* v_buildTime_7602_; lean_object* v___x_7604_; uint8_t v_isShared_7605_; uint8_t v_isSharedCheck_7634_; 
v_log_7598_ = lean_ctor_get(v___y_7596_, 0);
v_action_7599_ = lean_ctor_get_uint8(v___y_7596_, sizeof(void*)*3);
v_wantsRebuild_7600_ = lean_ctor_get_uint8(v___y_7596_, sizeof(void*)*3 + 1);
v_trace_7601_ = lean_ctor_get(v___y_7596_, 1);
v_buildTime_7602_ = lean_ctor_get(v___y_7596_, 2);
v_isSharedCheck_7634_ = !lean_is_exclusive(v___y_7596_);
if (v_isSharedCheck_7634_ == 0)
{
v___x_7604_ = v___y_7596_;
v_isShared_7605_ = v_isSharedCheck_7634_;
goto v_resetjp_7603_;
}
else
{
lean_inc(v_buildTime_7602_);
lean_inc(v_trace_7601_);
lean_inc(v_log_7598_);
lean_dec(v___y_7596_);
v___x_7604_ = lean_box(0);
v_isShared_7605_ = v_isSharedCheck_7634_;
goto v_resetjp_7603_;
}
v_resetjp_7603_:
{
lean_object* v___x_7606_; lean_object* v___x_7607_; lean_object* v___x_7608_; lean_object* v___x_7609_; 
v___x_7606_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7585_, v_libs_7590_);
v___x_7607_ = l_Array_append___redArg(v___x_7606_, v_weakArgs_7586_);
v___x_7608_ = l_Array_append___redArg(v___x_7607_, v_traceArgs_7587_);
v___x_7609_ = l_Lake_compileSharedLib(v_libFile_7588_, v___x_7608_, v_linker_7589_, v_log_7598_);
lean_dec_ref(v___x_7608_);
if (lean_obj_tag(v___x_7609_) == 0)
{
lean_object* v_a_7610_; lean_object* v_a_7611_; lean_object* v___x_7613_; uint8_t v_isShared_7614_; uint8_t v_isSharedCheck_7621_; 
v_a_7610_ = lean_ctor_get(v___x_7609_, 0);
v_a_7611_ = lean_ctor_get(v___x_7609_, 1);
v_isSharedCheck_7621_ = !lean_is_exclusive(v___x_7609_);
if (v_isSharedCheck_7621_ == 0)
{
v___x_7613_ = v___x_7609_;
v_isShared_7614_ = v_isSharedCheck_7621_;
goto v_resetjp_7612_;
}
else
{
lean_inc(v_a_7611_);
lean_inc(v_a_7610_);
lean_dec(v___x_7609_);
v___x_7613_ = lean_box(0);
v_isShared_7614_ = v_isSharedCheck_7621_;
goto v_resetjp_7612_;
}
v_resetjp_7612_:
{
lean_object* v___x_7616_; 
if (v_isShared_7605_ == 0)
{
lean_ctor_set(v___x_7604_, 0, v_a_7611_);
v___x_7616_ = v___x_7604_;
goto v_reusejp_7615_;
}
else
{
lean_object* v_reuseFailAlloc_7620_; 
v_reuseFailAlloc_7620_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7620_, 0, v_a_7611_);
lean_ctor_set(v_reuseFailAlloc_7620_, 1, v_trace_7601_);
lean_ctor_set(v_reuseFailAlloc_7620_, 2, v_buildTime_7602_);
lean_ctor_set_uint8(v_reuseFailAlloc_7620_, sizeof(void*)*3, v_action_7599_);
lean_ctor_set_uint8(v_reuseFailAlloc_7620_, sizeof(void*)*3 + 1, v_wantsRebuild_7600_);
v___x_7616_ = v_reuseFailAlloc_7620_;
goto v_reusejp_7615_;
}
v_reusejp_7615_:
{
lean_object* v___x_7618_; 
if (v_isShared_7614_ == 0)
{
lean_ctor_set(v___x_7613_, 1, v___x_7616_);
v___x_7618_ = v___x_7613_;
goto v_reusejp_7617_;
}
else
{
lean_object* v_reuseFailAlloc_7619_; 
v_reuseFailAlloc_7619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7619_, 0, v_a_7610_);
lean_ctor_set(v_reuseFailAlloc_7619_, 1, v___x_7616_);
v___x_7618_ = v_reuseFailAlloc_7619_;
goto v_reusejp_7617_;
}
v_reusejp_7617_:
{
return v___x_7618_;
}
}
}
}
else
{
lean_object* v_a_7622_; lean_object* v_a_7623_; lean_object* v___x_7625_; uint8_t v_isShared_7626_; uint8_t v_isSharedCheck_7633_; 
v_a_7622_ = lean_ctor_get(v___x_7609_, 0);
v_a_7623_ = lean_ctor_get(v___x_7609_, 1);
v_isSharedCheck_7633_ = !lean_is_exclusive(v___x_7609_);
if (v_isSharedCheck_7633_ == 0)
{
v___x_7625_ = v___x_7609_;
v_isShared_7626_ = v_isSharedCheck_7633_;
goto v_resetjp_7624_;
}
else
{
lean_inc(v_a_7623_);
lean_inc(v_a_7622_);
lean_dec(v___x_7609_);
v___x_7625_ = lean_box(0);
v_isShared_7626_ = v_isSharedCheck_7633_;
goto v_resetjp_7624_;
}
v_resetjp_7624_:
{
lean_object* v___x_7628_; 
if (v_isShared_7605_ == 0)
{
lean_ctor_set(v___x_7604_, 0, v_a_7623_);
v___x_7628_ = v___x_7604_;
goto v_reusejp_7627_;
}
else
{
lean_object* v_reuseFailAlloc_7632_; 
v_reuseFailAlloc_7632_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7632_, 0, v_a_7623_);
lean_ctor_set(v_reuseFailAlloc_7632_, 1, v_trace_7601_);
lean_ctor_set(v_reuseFailAlloc_7632_, 2, v_buildTime_7602_);
lean_ctor_set_uint8(v_reuseFailAlloc_7632_, sizeof(void*)*3, v_action_7599_);
lean_ctor_set_uint8(v_reuseFailAlloc_7632_, sizeof(void*)*3 + 1, v_wantsRebuild_7600_);
v___x_7628_ = v_reuseFailAlloc_7632_;
goto v_reusejp_7627_;
}
v_reusejp_7627_:
{
lean_object* v___x_7630_; 
if (v_isShared_7626_ == 0)
{
lean_ctor_set(v___x_7625_, 1, v___x_7628_);
v___x_7630_ = v___x_7625_;
goto v_reusejp_7629_;
}
else
{
lean_object* v_reuseFailAlloc_7631_; 
v_reuseFailAlloc_7631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7631_, 0, v_a_7622_);
lean_ctor_set(v_reuseFailAlloc_7631_, 1, v___x_7628_);
v___x_7630_ = v_reuseFailAlloc_7631_;
goto v_reusejp_7629_;
}
v_reusejp_7629_:
{
return v___x_7630_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7635_, lean_object* v_weakArgs_7636_, lean_object* v_traceArgs_7637_, lean_object* v_libFile_7638_, lean_object* v_linker_7639_, lean_object* v_libs_7640_, lean_object* v___y_7641_, lean_object* v___y_7642_, lean_object* v___y_7643_, lean_object* v___y_7644_, lean_object* v___y_7645_, lean_object* v___y_7646_, lean_object* v___y_7647_){
_start:
{
lean_object* v_res_7648_; 
v_res_7648_ = l_Lake_buildSharedLib___lam__0(v_objs_7635_, v_weakArgs_7636_, v_traceArgs_7637_, v_libFile_7638_, v_linker_7639_, v_libs_7640_, v___y_7641_, v___y_7642_, v___y_7643_, v___y_7644_, v___y_7645_, v___y_7646_);
lean_dec_ref(v___y_7645_);
lean_dec(v___y_7644_);
lean_dec(v___y_7643_);
lean_dec(v___y_7642_);
lean_dec_ref(v___y_7641_);
lean_dec_ref(v_libs_7640_);
lean_dec_ref(v_traceArgs_7637_);
lean_dec_ref(v_weakArgs_7636_);
lean_dec_ref(v_objs_7635_);
return v_res_7648_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7649_, lean_object* v___x_7650_, lean_object* v___f_7651_, lean_object* v_libs_7652_, lean_object* v___y_7653_, lean_object* v___y_7654_, lean_object* v___y_7655_, lean_object* v___y_7656_, lean_object* v___y_7657_, lean_object* v___y_7658_){
_start:
{
if (v_linkDeps_7649_ == 0)
{
lean_object* v___x_7660_; lean_object* v___x_7661_; 
v___x_7660_ = lean_mk_empty_array_with_capacity(v___x_7650_);
lean_inc_ref(v___y_7657_);
lean_inc(v___y_7656_);
lean_inc(v___y_7655_);
lean_inc(v___y_7654_);
v___x_7661_ = lean_apply_8(v___f_7651_, v___x_7660_, v___y_7653_, v___y_7654_, v___y_7655_, v___y_7656_, v___y_7657_, v___y_7658_, lean_box(0));
return v___x_7661_;
}
else
{
lean_object* v___x_7662_; 
v___x_7662_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7652_, v___y_7658_);
if (lean_obj_tag(v___x_7662_) == 0)
{
lean_object* v_a_7663_; lean_object* v_a_7664_; lean_object* v___x_7665_; 
v_a_7663_ = lean_ctor_get(v___x_7662_, 0);
lean_inc(v_a_7663_);
v_a_7664_ = lean_ctor_get(v___x_7662_, 1);
lean_inc(v_a_7664_);
lean_dec_ref_known(v___x_7662_, 2);
lean_inc_ref(v___y_7657_);
lean_inc(v___y_7656_);
lean_inc(v___y_7655_);
lean_inc(v___y_7654_);
v___x_7665_ = lean_apply_8(v___f_7651_, v_a_7663_, v___y_7653_, v___y_7654_, v___y_7655_, v___y_7656_, v___y_7657_, v_a_7664_, lean_box(0));
return v___x_7665_;
}
else
{
lean_object* v_a_7666_; lean_object* v_a_7667_; lean_object* v___x_7669_; uint8_t v_isShared_7670_; uint8_t v_isSharedCheck_7674_; 
lean_dec_ref(v___y_7653_);
lean_dec_ref(v___f_7651_);
v_a_7666_ = lean_ctor_get(v___x_7662_, 0);
v_a_7667_ = lean_ctor_get(v___x_7662_, 1);
v_isSharedCheck_7674_ = !lean_is_exclusive(v___x_7662_);
if (v_isSharedCheck_7674_ == 0)
{
v___x_7669_ = v___x_7662_;
v_isShared_7670_ = v_isSharedCheck_7674_;
goto v_resetjp_7668_;
}
else
{
lean_inc(v_a_7667_);
lean_inc(v_a_7666_);
lean_dec(v___x_7662_);
v___x_7669_ = lean_box(0);
v_isShared_7670_ = v_isSharedCheck_7674_;
goto v_resetjp_7668_;
}
v_resetjp_7668_:
{
lean_object* v___x_7672_; 
if (v_isShared_7670_ == 0)
{
v___x_7672_ = v___x_7669_;
goto v_reusejp_7671_;
}
else
{
lean_object* v_reuseFailAlloc_7673_; 
v_reuseFailAlloc_7673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7673_, 0, v_a_7666_);
lean_ctor_set(v_reuseFailAlloc_7673_, 1, v_a_7667_);
v___x_7672_ = v_reuseFailAlloc_7673_;
goto v_reusejp_7671_;
}
v_reusejp_7671_:
{
return v___x_7672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7675_, lean_object* v___x_7676_, lean_object* v___f_7677_, lean_object* v_libs_7678_, lean_object* v___y_7679_, lean_object* v___y_7680_, lean_object* v___y_7681_, lean_object* v___y_7682_, lean_object* v___y_7683_, lean_object* v___y_7684_, lean_object* v___y_7685_){
_start:
{
uint8_t v_linkDeps_boxed_7686_; lean_object* v_res_7687_; 
v_linkDeps_boxed_7686_ = lean_unbox(v_linkDeps_7675_);
v_res_7687_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7686_, v___x_7676_, v___f_7677_, v_libs_7678_, v___y_7679_, v___y_7680_, v___y_7681_, v___y_7682_, v___y_7683_, v___y_7684_);
lean_dec_ref(v___y_7683_);
lean_dec(v___y_7682_);
lean_dec(v___y_7681_);
lean_dec(v___y_7680_);
lean_dec_ref(v_libs_7678_);
lean_dec(v___x_7676_);
return v_res_7687_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7688_, lean_object* v_extraDepTrace_7689_, uint8_t v_linkDeps_7690_, lean_object* v___f_7691_, lean_object* v_libFile_7692_, lean_object* v_libName_7693_, uint8_t v_plugin_7694_, lean_object* v_libs_7695_, lean_object* v___y_7696_, lean_object* v___y_7697_, lean_object* v___y_7698_, lean_object* v___y_7699_, lean_object* v___y_7700_, lean_object* v___y_7701_){
_start:
{
uint64_t v___y_7704_; uint64_t v___x_7781_; lean_object* v___x_7782_; lean_object* v___x_7783_; uint8_t v___x_7784_; 
v___x_7781_ = l_Lake_Hash_nil;
v___x_7782_ = lean_unsigned_to_nat(0u);
v___x_7783_ = lean_array_get_size(v_traceArgs_7688_);
v___x_7784_ = lean_nat_dec_lt(v___x_7782_, v___x_7783_);
if (v___x_7784_ == 0)
{
v___y_7704_ = v___x_7781_;
goto v___jp_7703_;
}
else
{
uint8_t v___x_7785_; 
v___x_7785_ = lean_nat_dec_le(v___x_7783_, v___x_7783_);
if (v___x_7785_ == 0)
{
if (v___x_7784_ == 0)
{
v___y_7704_ = v___x_7781_;
goto v___jp_7703_;
}
else
{
size_t v___x_7786_; size_t v___x_7787_; uint64_t v___x_7788_; 
v___x_7786_ = ((size_t)0ULL);
v___x_7787_ = lean_usize_of_nat(v___x_7783_);
v___x_7788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7688_, v___x_7786_, v___x_7787_, v___x_7781_);
v___y_7704_ = v___x_7788_;
goto v___jp_7703_;
}
}
else
{
size_t v___x_7789_; size_t v___x_7790_; uint64_t v___x_7791_; 
v___x_7789_ = ((size_t)0ULL);
v___x_7790_ = lean_usize_of_nat(v___x_7783_);
v___x_7791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7688_, v___x_7789_, v___x_7790_, v___x_7781_);
v___y_7704_ = v___x_7791_;
goto v___jp_7703_;
}
}
v___jp_7703_:
{
lean_object* v_log_7705_; uint8_t v_action_7706_; uint8_t v_wantsRebuild_7707_; lean_object* v_trace_7708_; lean_object* v_buildTime_7709_; lean_object* v___x_7711_; uint8_t v_isShared_7712_; uint8_t v_isSharedCheck_7780_; 
v_log_7705_ = lean_ctor_get(v___y_7701_, 0);
v_action_7706_ = lean_ctor_get_uint8(v___y_7701_, sizeof(void*)*3);
v_wantsRebuild_7707_ = lean_ctor_get_uint8(v___y_7701_, sizeof(void*)*3 + 1);
v_trace_7708_ = lean_ctor_get(v___y_7701_, 1);
v_buildTime_7709_ = lean_ctor_get(v___y_7701_, 2);
v_isSharedCheck_7780_ = !lean_is_exclusive(v___y_7701_);
if (v_isSharedCheck_7780_ == 0)
{
v___x_7711_ = v___y_7701_;
v_isShared_7712_ = v_isSharedCheck_7780_;
goto v_resetjp_7710_;
}
else
{
lean_inc(v_buildTime_7709_);
lean_inc(v_trace_7708_);
lean_inc(v_log_7705_);
lean_dec(v___y_7701_);
v___x_7711_ = lean_box(0);
v_isShared_7712_ = v_isSharedCheck_7780_;
goto v_resetjp_7710_;
}
v_resetjp_7710_:
{
lean_object* v___x_7713_; lean_object* v___x_7714_; lean_object* v___x_7715_; lean_object* v___x_7716_; lean_object* v___x_7717_; lean_object* v___x_7718_; lean_object* v___x_7719_; lean_object* v___x_7720_; lean_object* v___x_7721_; lean_object* v___x_7722_; lean_object* v___x_7723_; lean_object* v___x_7724_; lean_object* v___x_7725_; lean_object* v___x_7727_; 
v___x_7713_ = lean_unsigned_to_nat(0u);
v___x_7714_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7715_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7716_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7717_ = lean_array_to_list(v_traceArgs_7688_);
v___x_7718_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7717_);
lean_dec(v___x_7717_);
v___x_7719_ = lean_string_append(v___x_7716_, v___x_7718_);
lean_dec_ref(v___x_7718_);
v___x_7720_ = lean_string_append(v___x_7715_, v___x_7719_);
lean_dec_ref(v___x_7719_);
v___x_7721_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7722_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7722_, 0, v___x_7720_);
lean_ctor_set(v___x_7722_, 1, v___x_7714_);
lean_ctor_set(v___x_7722_, 2, v___x_7721_);
lean_ctor_set_uint64(v___x_7722_, sizeof(void*)*3, v___y_7704_);
v___x_7723_ = l_Lake_BuildTrace_mix(v_trace_7708_, v___x_7722_);
v___x_7724_ = l_Lake_platformTrace;
v___x_7725_ = l_Lake_BuildTrace_mix(v___x_7723_, v___x_7724_);
if (v_isShared_7712_ == 0)
{
lean_ctor_set(v___x_7711_, 1, v___x_7725_);
v___x_7727_ = v___x_7711_;
goto v_reusejp_7726_;
}
else
{
lean_object* v_reuseFailAlloc_7779_; 
v_reuseFailAlloc_7779_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7779_, 0, v_log_7705_);
lean_ctor_set(v_reuseFailAlloc_7779_, 1, v___x_7725_);
lean_ctor_set(v_reuseFailAlloc_7779_, 2, v_buildTime_7709_);
lean_ctor_set_uint8(v_reuseFailAlloc_7779_, sizeof(void*)*3, v_action_7706_);
lean_ctor_set_uint8(v_reuseFailAlloc_7779_, sizeof(void*)*3 + 1, v_wantsRebuild_7707_);
v___x_7727_ = v_reuseFailAlloc_7779_;
goto v_reusejp_7726_;
}
v_reusejp_7726_:
{
lean_object* v___x_7728_; 
lean_inc_ref(v___y_7700_);
lean_inc(v___y_7699_);
lean_inc(v___y_7698_);
lean_inc(v___y_7697_);
lean_inc_ref(v___y_7696_);
v___x_7728_ = lean_apply_7(v_extraDepTrace_7689_, v___y_7696_, v___y_7697_, v___y_7698_, v___y_7699_, v___y_7700_, v___x_7727_, lean_box(0));
if (lean_obj_tag(v___x_7728_) == 0)
{
lean_object* v_a_7729_; lean_object* v_a_7730_; lean_object* v_log_7731_; uint8_t v_action_7732_; uint8_t v_wantsRebuild_7733_; lean_object* v_trace_7734_; lean_object* v_buildTime_7735_; lean_object* v___x_7737_; uint8_t v_isShared_7738_; uint8_t v_isSharedCheck_7769_; 
v_a_7729_ = lean_ctor_get(v___x_7728_, 1);
lean_inc(v_a_7729_);
v_a_7730_ = lean_ctor_get(v___x_7728_, 0);
lean_inc(v_a_7730_);
lean_dec_ref_known(v___x_7728_, 2);
v_log_7731_ = lean_ctor_get(v_a_7729_, 0);
v_action_7732_ = lean_ctor_get_uint8(v_a_7729_, sizeof(void*)*3);
v_wantsRebuild_7733_ = lean_ctor_get_uint8(v_a_7729_, sizeof(void*)*3 + 1);
v_trace_7734_ = lean_ctor_get(v_a_7729_, 1);
v_buildTime_7735_ = lean_ctor_get(v_a_7729_, 2);
v_isSharedCheck_7769_ = !lean_is_exclusive(v_a_7729_);
if (v_isSharedCheck_7769_ == 0)
{
v___x_7737_ = v_a_7729_;
v_isShared_7738_ = v_isSharedCheck_7769_;
goto v_resetjp_7736_;
}
else
{
lean_inc(v_buildTime_7735_);
lean_inc(v_trace_7734_);
lean_inc(v_log_7731_);
lean_dec(v_a_7729_);
v___x_7737_ = lean_box(0);
v_isShared_7738_ = v_isSharedCheck_7769_;
goto v_resetjp_7736_;
}
v_resetjp_7736_:
{
lean_object* v___x_7739_; lean_object* v___y_7740_; lean_object* v___x_7741_; lean_object* v___x_7743_; 
v___x_7739_ = lean_box(v_linkDeps_7690_);
lean_inc_ref(v_libs_7695_);
v___y_7740_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7740_, 0, v___x_7739_);
lean_closure_set(v___y_7740_, 1, v___x_7713_);
lean_closure_set(v___y_7740_, 2, v___f_7691_);
lean_closure_set(v___y_7740_, 3, v_libs_7695_);
v___x_7741_ = l_Lake_BuildTrace_mix(v_trace_7734_, v_a_7730_);
if (v_isShared_7738_ == 0)
{
lean_ctor_set(v___x_7737_, 1, v___x_7741_);
v___x_7743_ = v___x_7737_;
goto v_reusejp_7742_;
}
else
{
lean_object* v_reuseFailAlloc_7768_; 
v_reuseFailAlloc_7768_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7768_, 0, v_log_7731_);
lean_ctor_set(v_reuseFailAlloc_7768_, 1, v___x_7741_);
lean_ctor_set(v_reuseFailAlloc_7768_, 2, v_buildTime_7735_);
lean_ctor_set_uint8(v_reuseFailAlloc_7768_, sizeof(void*)*3, v_action_7732_);
lean_ctor_set_uint8(v_reuseFailAlloc_7768_, sizeof(void*)*3 + 1, v_wantsRebuild_7733_);
v___x_7743_ = v_reuseFailAlloc_7768_;
goto v_reusejp_7742_;
}
v_reusejp_7742_:
{
uint8_t v___x_7744_; uint8_t v___x_7745_; lean_object* v___x_7746_; lean_object* v___x_7747_; 
v___x_7744_ = 1;
v___x_7745_ = 0;
v___x_7746_ = l_Lake_sharedLibExt;
v___x_7747_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7692_, v___y_7740_, v___x_7745_, v___x_7746_, v___x_7744_, v___x_7745_, v___x_7745_, v___y_7696_, v___y_7697_, v___y_7698_, v___y_7699_, v___y_7700_, v___x_7743_);
if (lean_obj_tag(v___x_7747_) == 0)
{
lean_object* v_a_7748_; lean_object* v_a_7749_; lean_object* v___x_7751_; uint8_t v_isShared_7752_; uint8_t v_isSharedCheck_7758_; 
v_a_7748_ = lean_ctor_get(v___x_7747_, 0);
v_a_7749_ = lean_ctor_get(v___x_7747_, 1);
v_isSharedCheck_7758_ = !lean_is_exclusive(v___x_7747_);
if (v_isSharedCheck_7758_ == 0)
{
v___x_7751_ = v___x_7747_;
v_isShared_7752_ = v_isSharedCheck_7758_;
goto v_resetjp_7750_;
}
else
{
lean_inc(v_a_7749_);
lean_inc(v_a_7748_);
lean_dec(v___x_7747_);
v___x_7751_ = lean_box(0);
v_isShared_7752_ = v_isSharedCheck_7758_;
goto v_resetjp_7750_;
}
v_resetjp_7750_:
{
lean_object* v_path_7753_; lean_object* v___x_7754_; lean_object* v___x_7756_; 
v_path_7753_ = lean_ctor_get(v_a_7748_, 1);
lean_inc_ref(v_path_7753_);
lean_dec(v_a_7748_);
v___x_7754_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7754_, 0, v_path_7753_);
lean_ctor_set(v___x_7754_, 1, v_libName_7693_);
lean_ctor_set(v___x_7754_, 2, v_libs_7695_);
lean_ctor_set_uint8(v___x_7754_, sizeof(void*)*3, v_plugin_7694_);
if (v_isShared_7752_ == 0)
{
lean_ctor_set(v___x_7751_, 0, v___x_7754_);
v___x_7756_ = v___x_7751_;
goto v_reusejp_7755_;
}
else
{
lean_object* v_reuseFailAlloc_7757_; 
v_reuseFailAlloc_7757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7757_, 0, v___x_7754_);
lean_ctor_set(v_reuseFailAlloc_7757_, 1, v_a_7749_);
v___x_7756_ = v_reuseFailAlloc_7757_;
goto v_reusejp_7755_;
}
v_reusejp_7755_:
{
return v___x_7756_;
}
}
}
else
{
lean_object* v_a_7759_; lean_object* v_a_7760_; lean_object* v___x_7762_; uint8_t v_isShared_7763_; uint8_t v_isSharedCheck_7767_; 
lean_dec_ref(v_libs_7695_);
lean_dec_ref(v_libName_7693_);
v_a_7759_ = lean_ctor_get(v___x_7747_, 0);
v_a_7760_ = lean_ctor_get(v___x_7747_, 1);
v_isSharedCheck_7767_ = !lean_is_exclusive(v___x_7747_);
if (v_isSharedCheck_7767_ == 0)
{
v___x_7762_ = v___x_7747_;
v_isShared_7763_ = v_isSharedCheck_7767_;
goto v_resetjp_7761_;
}
else
{
lean_inc(v_a_7760_);
lean_inc(v_a_7759_);
lean_dec(v___x_7747_);
v___x_7762_ = lean_box(0);
v_isShared_7763_ = v_isSharedCheck_7767_;
goto v_resetjp_7761_;
}
v_resetjp_7761_:
{
lean_object* v___x_7765_; 
if (v_isShared_7763_ == 0)
{
v___x_7765_ = v___x_7762_;
goto v_reusejp_7764_;
}
else
{
lean_object* v_reuseFailAlloc_7766_; 
v_reuseFailAlloc_7766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7766_, 0, v_a_7759_);
lean_ctor_set(v_reuseFailAlloc_7766_, 1, v_a_7760_);
v___x_7765_ = v_reuseFailAlloc_7766_;
goto v_reusejp_7764_;
}
v_reusejp_7764_:
{
return v___x_7765_;
}
}
}
}
}
}
else
{
lean_object* v_a_7770_; lean_object* v_a_7771_; lean_object* v___x_7773_; uint8_t v_isShared_7774_; uint8_t v_isSharedCheck_7778_; 
lean_dec_ref(v___y_7696_);
lean_dec_ref(v_libs_7695_);
lean_dec_ref(v_libName_7693_);
lean_dec_ref(v_libFile_7692_);
lean_dec_ref(v___f_7691_);
v_a_7770_ = lean_ctor_get(v___x_7728_, 0);
v_a_7771_ = lean_ctor_get(v___x_7728_, 1);
v_isSharedCheck_7778_ = !lean_is_exclusive(v___x_7728_);
if (v_isSharedCheck_7778_ == 0)
{
v___x_7773_ = v___x_7728_;
v_isShared_7774_ = v_isSharedCheck_7778_;
goto v_resetjp_7772_;
}
else
{
lean_inc(v_a_7771_);
lean_inc(v_a_7770_);
lean_dec(v___x_7728_);
v___x_7773_ = lean_box(0);
v_isShared_7774_ = v_isSharedCheck_7778_;
goto v_resetjp_7772_;
}
v_resetjp_7772_:
{
lean_object* v___x_7776_; 
if (v_isShared_7774_ == 0)
{
v___x_7776_ = v___x_7773_;
goto v_reusejp_7775_;
}
else
{
lean_object* v_reuseFailAlloc_7777_; 
v_reuseFailAlloc_7777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7777_, 0, v_a_7770_);
lean_ctor_set(v_reuseFailAlloc_7777_, 1, v_a_7771_);
v___x_7776_ = v_reuseFailAlloc_7777_;
goto v_reusejp_7775_;
}
v_reusejp_7775_:
{
return v___x_7776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7792_, lean_object* v_extraDepTrace_7793_, lean_object* v_linkDeps_7794_, lean_object* v___f_7795_, lean_object* v_libFile_7796_, lean_object* v_libName_7797_, lean_object* v_plugin_7798_, lean_object* v_libs_7799_, lean_object* v___y_7800_, lean_object* v___y_7801_, lean_object* v___y_7802_, lean_object* v___y_7803_, lean_object* v___y_7804_, lean_object* v___y_7805_, lean_object* v___y_7806_){
_start:
{
uint8_t v_linkDeps_boxed_7807_; uint8_t v_plugin_boxed_7808_; lean_object* v_res_7809_; 
v_linkDeps_boxed_7807_ = lean_unbox(v_linkDeps_7794_);
v_plugin_boxed_7808_ = lean_unbox(v_plugin_7798_);
v_res_7809_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7792_, v_extraDepTrace_7793_, v_linkDeps_boxed_7807_, v___f_7795_, v_libFile_7796_, v_libName_7797_, v_plugin_boxed_7808_, v_libs_7799_, v___y_7800_, v___y_7801_, v___y_7802_, v___y_7803_, v___y_7804_, v___y_7805_);
lean_dec_ref(v___y_7804_);
lean_dec(v___y_7803_);
lean_dec(v___y_7802_);
lean_dec(v___y_7801_);
return v_res_7809_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7811_, lean_object* v_traceArgs_7812_, lean_object* v_libFile_7813_, lean_object* v_linker_7814_, lean_object* v_extraDepTrace_7815_, uint8_t v_linkDeps_7816_, lean_object* v_libName_7817_, uint8_t v_plugin_7818_, lean_object* v_linkLibs_7819_, lean_object* v___x_7820_, lean_object* v_objs_7821_, lean_object* v___y_7822_, lean_object* v___y_7823_, lean_object* v___y_7824_, lean_object* v___y_7825_, lean_object* v___y_7826_, lean_object* v___y_7827_){
_start:
{
lean_object* v_trace_7829_; lean_object* v___f_7830_; lean_object* v___x_7831_; lean_object* v___x_7832_; lean_object* v___f_7833_; lean_object* v___x_7834_; lean_object* v___x_7835_; lean_object* v___x_7836_; uint8_t v___x_7837_; lean_object* v___x_7838_; lean_object* v___x_7839_; 
v_trace_7829_ = lean_ctor_get(v___y_7827_, 1);
lean_inc_ref(v_libFile_7813_);
lean_inc_ref(v_traceArgs_7812_);
v___f_7830_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7830_, 0, v_objs_7821_);
lean_closure_set(v___f_7830_, 1, v_weakArgs_7811_);
lean_closure_set(v___f_7830_, 2, v_traceArgs_7812_);
lean_closure_set(v___f_7830_, 3, v_libFile_7813_);
lean_closure_set(v___f_7830_, 4, v_linker_7814_);
v___x_7831_ = lean_box(v_linkDeps_7816_);
v___x_7832_ = lean_box(v_plugin_7818_);
v___f_7833_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7833_, 0, v_traceArgs_7812_);
lean_closure_set(v___f_7833_, 1, v_extraDepTrace_7815_);
lean_closure_set(v___f_7833_, 2, v___x_7831_);
lean_closure_set(v___f_7833_, 3, v___f_7830_);
lean_closure_set(v___f_7833_, 4, v_libFile_7813_);
lean_closure_set(v___f_7833_, 5, v_libName_7817_);
lean_closure_set(v___f_7833_, 6, v___x_7832_);
v___x_7834_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7835_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7819_, v___x_7834_);
v___x_7836_ = lean_unsigned_to_nat(0u);
v___x_7837_ = 0;
v___x_7838_ = l_Lake_Job_mapM___redArg(v___x_7820_, v___x_7835_, v___f_7833_, v___x_7836_, v___x_7837_, v___y_7822_, v___y_7823_, v___y_7824_, v___y_7825_, v___y_7826_, v_trace_7829_);
v___x_7839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7839_, 0, v___x_7838_);
lean_ctor_set(v___x_7839_, 1, v___y_7827_);
return v___x_7839_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7840_ = _args[0];
lean_object* v_traceArgs_7841_ = _args[1];
lean_object* v_libFile_7842_ = _args[2];
lean_object* v_linker_7843_ = _args[3];
lean_object* v_extraDepTrace_7844_ = _args[4];
lean_object* v_linkDeps_7845_ = _args[5];
lean_object* v_libName_7846_ = _args[6];
lean_object* v_plugin_7847_ = _args[7];
lean_object* v_linkLibs_7848_ = _args[8];
lean_object* v___x_7849_ = _args[9];
lean_object* v_objs_7850_ = _args[10];
lean_object* v___y_7851_ = _args[11];
lean_object* v___y_7852_ = _args[12];
lean_object* v___y_7853_ = _args[13];
lean_object* v___y_7854_ = _args[14];
lean_object* v___y_7855_ = _args[15];
lean_object* v___y_7856_ = _args[16];
lean_object* v___y_7857_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7858_; uint8_t v_plugin_boxed_7859_; lean_object* v_res_7860_; 
v_linkDeps_boxed_7858_ = lean_unbox(v_linkDeps_7845_);
v_plugin_boxed_7859_ = lean_unbox(v_plugin_7847_);
v_res_7860_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7840_, v_traceArgs_7841_, v_libFile_7842_, v_linker_7843_, v_extraDepTrace_7844_, v_linkDeps_boxed_7858_, v_libName_7846_, v_plugin_boxed_7859_, v_linkLibs_7848_, v___x_7849_, v_objs_7850_, v___y_7851_, v___y_7852_, v___y_7853_, v___y_7854_, v___y_7855_, v___y_7856_);
lean_dec_ref(v___y_7855_);
lean_dec(v___y_7854_);
lean_dec(v___y_7853_);
lean_dec(v___y_7852_);
lean_dec_ref(v_linkLibs_7848_);
return v_res_7860_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7862_, lean_object* v_libFile_7863_, lean_object* v_linkObjs_7864_, lean_object* v_linkLibs_7865_, lean_object* v_weakArgs_7866_, lean_object* v_traceArgs_7867_, lean_object* v_linker_7868_, lean_object* v_extraDepTrace_7869_, uint8_t v_plugin_7870_, uint8_t v_linkDeps_7871_, lean_object* v_a_7872_, lean_object* v_a_7873_, lean_object* v_a_7874_, lean_object* v_a_7875_, lean_object* v_a_7876_, lean_object* v_a_7877_){
_start:
{
lean_object* v___x_7879_; lean_object* v___x_7880_; lean_object* v___x_7881_; lean_object* v___f_7882_; lean_object* v___x_7883_; lean_object* v___x_7884_; lean_object* v___x_7885_; uint8_t v___x_7886_; lean_object* v___x_7887_; 
v___x_7879_ = l_Lake_instDataKindDynlib;
v___x_7880_ = lean_box(v_linkDeps_7871_);
v___x_7881_ = lean_box(v_plugin_7870_);
v___f_7882_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7882_, 0, v_weakArgs_7866_);
lean_closure_set(v___f_7882_, 1, v_traceArgs_7867_);
lean_closure_set(v___f_7882_, 2, v_libFile_7863_);
lean_closure_set(v___f_7882_, 3, v_linker_7868_);
lean_closure_set(v___f_7882_, 4, v_extraDepTrace_7869_);
lean_closure_set(v___f_7882_, 5, v___x_7880_);
lean_closure_set(v___f_7882_, 6, v_libName_7862_);
lean_closure_set(v___f_7882_, 7, v___x_7881_);
lean_closure_set(v___f_7882_, 8, v_linkLibs_7865_);
lean_closure_set(v___f_7882_, 9, v___x_7879_);
v___x_7883_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7884_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7864_, v___x_7883_);
v___x_7885_ = lean_unsigned_to_nat(0u);
v___x_7886_ = 1;
v___x_7887_ = l_Lake_Job_bindM___redArg(v___x_7879_, v___x_7884_, v___f_7882_, v___x_7885_, v___x_7886_, v_a_7872_, v_a_7873_, v_a_7874_, v_a_7875_, v_a_7876_, v_a_7877_);
return v___x_7887_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7888_ = _args[0];
lean_object* v_libFile_7889_ = _args[1];
lean_object* v_linkObjs_7890_ = _args[2];
lean_object* v_linkLibs_7891_ = _args[3];
lean_object* v_weakArgs_7892_ = _args[4];
lean_object* v_traceArgs_7893_ = _args[5];
lean_object* v_linker_7894_ = _args[6];
lean_object* v_extraDepTrace_7895_ = _args[7];
lean_object* v_plugin_7896_ = _args[8];
lean_object* v_linkDeps_7897_ = _args[9];
lean_object* v_a_7898_ = _args[10];
lean_object* v_a_7899_ = _args[11];
lean_object* v_a_7900_ = _args[12];
lean_object* v_a_7901_ = _args[13];
lean_object* v_a_7902_ = _args[14];
lean_object* v_a_7903_ = _args[15];
lean_object* v_a_7904_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7905_; uint8_t v_linkDeps_boxed_7906_; lean_object* v_res_7907_; 
v_plugin_boxed_7905_ = lean_unbox(v_plugin_7896_);
v_linkDeps_boxed_7906_ = lean_unbox(v_linkDeps_7897_);
v_res_7907_ = l_Lake_buildSharedLib(v_libName_7888_, v_libFile_7889_, v_linkObjs_7890_, v_linkLibs_7891_, v_weakArgs_7892_, v_traceArgs_7893_, v_linker_7894_, v_extraDepTrace_7895_, v_plugin_boxed_7905_, v_linkDeps_boxed_7906_, v_a_7898_, v_a_7899_, v_a_7900_, v_a_7901_, v_a_7902_, v_a_7903_);
lean_dec_ref(v_a_7903_);
lean_dec_ref(v_a_7902_);
lean_dec(v_a_7901_);
lean_dec(v_a_7900_);
lean_dec(v_a_7899_);
lean_dec_ref(v_linkObjs_7890_);
return v_res_7907_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7908_; lean_object* v___x_7909_; lean_object* v___x_7910_; lean_object* v___x_7911_; 
v___x_7908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7909_ = lean_unsigned_to_nat(2u);
v___x_7910_ = lean_mk_empty_array_with_capacity(v___x_7909_);
v___x_7911_ = lean_array_push(v___x_7910_, v___x_7908_);
return v___x_7911_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7912_, lean_object* v_weakArgs_7913_, lean_object* v_traceArgs_7914_, lean_object* v_libFile_7915_, uint8_t v_linkDeps_7916_, lean_object* v_libs_7917_, lean_object* v___y_7918_, lean_object* v___y_7919_, lean_object* v___y_7920_, lean_object* v___y_7921_, lean_object* v___y_7922_, lean_object* v___y_7923_){
_start:
{
lean_object* v_toContext_7925_; lean_object* v_lakeEnv_7926_; lean_object* v_lean_7927_; lean_object* v_libs_7929_; lean_object* v___y_7930_; 
v_toContext_7925_ = lean_ctor_get(v___y_7922_, 1);
v_lakeEnv_7926_ = lean_ctor_get(v_toContext_7925_, 0);
v_lean_7927_ = lean_ctor_get(v_lakeEnv_7926_, 1);
if (v_linkDeps_7916_ == 0)
{
lean_object* v___x_7975_; 
v___x_7975_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7929_ = v___x_7975_;
v___y_7930_ = v___y_7923_;
goto v___jp_7928_;
}
else
{
lean_object* v___x_7976_; 
v___x_7976_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7917_, v___y_7923_);
if (lean_obj_tag(v___x_7976_) == 0)
{
lean_object* v_a_7977_; lean_object* v_a_7978_; 
v_a_7977_ = lean_ctor_get(v___x_7976_, 0);
lean_inc(v_a_7977_);
v_a_7978_ = lean_ctor_get(v___x_7976_, 1);
lean_inc(v_a_7978_);
lean_dec_ref_known(v___x_7976_, 2);
v_libs_7929_ = v_a_7977_;
v___y_7930_ = v_a_7978_;
goto v___jp_7928_;
}
else
{
lean_object* v_a_7979_; lean_object* v_a_7980_; lean_object* v___x_7982_; uint8_t v_isShared_7983_; uint8_t v_isSharedCheck_7987_; 
lean_dec_ref(v_libFile_7915_);
v_a_7979_ = lean_ctor_get(v___x_7976_, 0);
v_a_7980_ = lean_ctor_get(v___x_7976_, 1);
v_isSharedCheck_7987_ = !lean_is_exclusive(v___x_7976_);
if (v_isSharedCheck_7987_ == 0)
{
v___x_7982_ = v___x_7976_;
v_isShared_7983_ = v_isSharedCheck_7987_;
goto v_resetjp_7981_;
}
else
{
lean_inc(v_a_7980_);
lean_inc(v_a_7979_);
lean_dec(v___x_7976_);
v___x_7982_ = lean_box(0);
v_isShared_7983_ = v_isSharedCheck_7987_;
goto v_resetjp_7981_;
}
v_resetjp_7981_:
{
lean_object* v___x_7985_; 
if (v_isShared_7983_ == 0)
{
v___x_7985_ = v___x_7982_;
goto v_reusejp_7984_;
}
else
{
lean_object* v_reuseFailAlloc_7986_; 
v_reuseFailAlloc_7986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7986_, 0, v_a_7979_);
lean_ctor_set(v_reuseFailAlloc_7986_, 1, v_a_7980_);
v___x_7985_ = v_reuseFailAlloc_7986_;
goto v_reusejp_7984_;
}
v_reusejp_7984_:
{
return v___x_7985_;
}
}
}
}
v___jp_7928_:
{
lean_object* v_leanLibDir_7931_; lean_object* v_cc_7932_; lean_object* v_ccLinkSharedFlags_7933_; lean_object* v_log_7934_; uint8_t v_action_7935_; uint8_t v_wantsRebuild_7936_; lean_object* v_trace_7937_; lean_object* v_buildTime_7938_; lean_object* v___x_7940_; uint8_t v_isShared_7941_; uint8_t v_isSharedCheck_7974_; 
v_leanLibDir_7931_ = lean_ctor_get(v_lean_7927_, 3);
v_cc_7932_ = lean_ctor_get(v_lean_7927_, 14);
v_ccLinkSharedFlags_7933_ = lean_ctor_get(v_lean_7927_, 20);
v_log_7934_ = lean_ctor_get(v___y_7930_, 0);
v_action_7935_ = lean_ctor_get_uint8(v___y_7930_, sizeof(void*)*3);
v_wantsRebuild_7936_ = lean_ctor_get_uint8(v___y_7930_, sizeof(void*)*3 + 1);
v_trace_7937_ = lean_ctor_get(v___y_7930_, 1);
v_buildTime_7938_ = lean_ctor_get(v___y_7930_, 2);
v_isSharedCheck_7974_ = !lean_is_exclusive(v___y_7930_);
if (v_isSharedCheck_7974_ == 0)
{
v___x_7940_ = v___y_7930_;
v_isShared_7941_ = v_isSharedCheck_7974_;
goto v_resetjp_7939_;
}
else
{
lean_inc(v_buildTime_7938_);
lean_inc(v_trace_7937_);
lean_inc(v_log_7934_);
lean_dec(v___y_7930_);
v___x_7940_ = lean_box(0);
v_isShared_7941_ = v_isSharedCheck_7974_;
goto v_resetjp_7939_;
}
v_resetjp_7939_:
{
lean_object* v___x_7942_; lean_object* v___x_7943_; lean_object* v___x_7944_; lean_object* v___x_7945_; lean_object* v___x_7946_; lean_object* v___x_7947_; lean_object* v___x_7948_; lean_object* v___x_7949_; 
v___x_7942_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7912_, v_libs_7929_);
lean_dec_ref(v_libs_7929_);
v___x_7943_ = l_Array_append___redArg(v___x_7942_, v_weakArgs_7913_);
v___x_7944_ = l_Array_append___redArg(v___x_7943_, v_traceArgs_7914_);
v___x_7945_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_7931_);
v___x_7946_ = lean_array_push(v___x_7945_, v_leanLibDir_7931_);
v___x_7947_ = l_Array_append___redArg(v___x_7944_, v___x_7946_);
lean_dec_ref(v___x_7946_);
v___x_7948_ = l_Array_append___redArg(v___x_7947_, v_ccLinkSharedFlags_7933_);
lean_inc_ref(v_cc_7932_);
v___x_7949_ = l_Lake_compileSharedLib(v_libFile_7915_, v___x_7948_, v_cc_7932_, v_log_7934_);
lean_dec_ref(v___x_7948_);
if (lean_obj_tag(v___x_7949_) == 0)
{
lean_object* v_a_7950_; lean_object* v_a_7951_; lean_object* v___x_7953_; uint8_t v_isShared_7954_; uint8_t v_isSharedCheck_7961_; 
v_a_7950_ = lean_ctor_get(v___x_7949_, 0);
v_a_7951_ = lean_ctor_get(v___x_7949_, 1);
v_isSharedCheck_7961_ = !lean_is_exclusive(v___x_7949_);
if (v_isSharedCheck_7961_ == 0)
{
v___x_7953_ = v___x_7949_;
v_isShared_7954_ = v_isSharedCheck_7961_;
goto v_resetjp_7952_;
}
else
{
lean_inc(v_a_7951_);
lean_inc(v_a_7950_);
lean_dec(v___x_7949_);
v___x_7953_ = lean_box(0);
v_isShared_7954_ = v_isSharedCheck_7961_;
goto v_resetjp_7952_;
}
v_resetjp_7952_:
{
lean_object* v___x_7956_; 
if (v_isShared_7941_ == 0)
{
lean_ctor_set(v___x_7940_, 0, v_a_7951_);
v___x_7956_ = v___x_7940_;
goto v_reusejp_7955_;
}
else
{
lean_object* v_reuseFailAlloc_7960_; 
v_reuseFailAlloc_7960_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7960_, 0, v_a_7951_);
lean_ctor_set(v_reuseFailAlloc_7960_, 1, v_trace_7937_);
lean_ctor_set(v_reuseFailAlloc_7960_, 2, v_buildTime_7938_);
lean_ctor_set_uint8(v_reuseFailAlloc_7960_, sizeof(void*)*3, v_action_7935_);
lean_ctor_set_uint8(v_reuseFailAlloc_7960_, sizeof(void*)*3 + 1, v_wantsRebuild_7936_);
v___x_7956_ = v_reuseFailAlloc_7960_;
goto v_reusejp_7955_;
}
v_reusejp_7955_:
{
lean_object* v___x_7958_; 
if (v_isShared_7954_ == 0)
{
lean_ctor_set(v___x_7953_, 1, v___x_7956_);
v___x_7958_ = v___x_7953_;
goto v_reusejp_7957_;
}
else
{
lean_object* v_reuseFailAlloc_7959_; 
v_reuseFailAlloc_7959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7959_, 0, v_a_7950_);
lean_ctor_set(v_reuseFailAlloc_7959_, 1, v___x_7956_);
v___x_7958_ = v_reuseFailAlloc_7959_;
goto v_reusejp_7957_;
}
v_reusejp_7957_:
{
return v___x_7958_;
}
}
}
}
else
{
lean_object* v_a_7962_; lean_object* v_a_7963_; lean_object* v___x_7965_; uint8_t v_isShared_7966_; uint8_t v_isSharedCheck_7973_; 
v_a_7962_ = lean_ctor_get(v___x_7949_, 0);
v_a_7963_ = lean_ctor_get(v___x_7949_, 1);
v_isSharedCheck_7973_ = !lean_is_exclusive(v___x_7949_);
if (v_isSharedCheck_7973_ == 0)
{
v___x_7965_ = v___x_7949_;
v_isShared_7966_ = v_isSharedCheck_7973_;
goto v_resetjp_7964_;
}
else
{
lean_inc(v_a_7963_);
lean_inc(v_a_7962_);
lean_dec(v___x_7949_);
v___x_7965_ = lean_box(0);
v_isShared_7966_ = v_isSharedCheck_7973_;
goto v_resetjp_7964_;
}
v_resetjp_7964_:
{
lean_object* v___x_7968_; 
if (v_isShared_7941_ == 0)
{
lean_ctor_set(v___x_7940_, 0, v_a_7963_);
v___x_7968_ = v___x_7940_;
goto v_reusejp_7967_;
}
else
{
lean_object* v_reuseFailAlloc_7972_; 
v_reuseFailAlloc_7972_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7972_, 0, v_a_7963_);
lean_ctor_set(v_reuseFailAlloc_7972_, 1, v_trace_7937_);
lean_ctor_set(v_reuseFailAlloc_7972_, 2, v_buildTime_7938_);
lean_ctor_set_uint8(v_reuseFailAlloc_7972_, sizeof(void*)*3, v_action_7935_);
lean_ctor_set_uint8(v_reuseFailAlloc_7972_, sizeof(void*)*3 + 1, v_wantsRebuild_7936_);
v___x_7968_ = v_reuseFailAlloc_7972_;
goto v_reusejp_7967_;
}
v_reusejp_7967_:
{
lean_object* v___x_7970_; 
if (v_isShared_7966_ == 0)
{
lean_ctor_set(v___x_7965_, 1, v___x_7968_);
v___x_7970_ = v___x_7965_;
goto v_reusejp_7969_;
}
else
{
lean_object* v_reuseFailAlloc_7971_; 
v_reuseFailAlloc_7971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7971_, 0, v_a_7962_);
lean_ctor_set(v_reuseFailAlloc_7971_, 1, v___x_7968_);
v___x_7970_ = v_reuseFailAlloc_7971_;
goto v_reusejp_7969_;
}
v_reusejp_7969_:
{
return v___x_7970_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7988_, lean_object* v_weakArgs_7989_, lean_object* v_traceArgs_7990_, lean_object* v_libFile_7991_, lean_object* v_linkDeps_7992_, lean_object* v_libs_7993_, lean_object* v___y_7994_, lean_object* v___y_7995_, lean_object* v___y_7996_, lean_object* v___y_7997_, lean_object* v___y_7998_, lean_object* v___y_7999_, lean_object* v___y_8000_){
_start:
{
uint8_t v_linkDeps_boxed_8001_; lean_object* v_res_8002_; 
v_linkDeps_boxed_8001_ = lean_unbox(v_linkDeps_7992_);
v_res_8002_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7988_, v_weakArgs_7989_, v_traceArgs_7990_, v_libFile_7991_, v_linkDeps_boxed_8001_, v_libs_7993_, v___y_7994_, v___y_7995_, v___y_7996_, v___y_7997_, v___y_7998_, v___y_7999_);
lean_dec_ref(v___y_7998_);
lean_dec(v___y_7997_);
lean_dec(v___y_7996_);
lean_dec(v___y_7995_);
lean_dec_ref(v___y_7994_);
lean_dec_ref(v_libs_7993_);
lean_dec_ref(v_traceArgs_7990_);
lean_dec_ref(v_weakArgs_7989_);
lean_dec_ref(v_objs_7988_);
return v_res_8002_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_8003_, lean_object* v_weakArgs_8004_, lean_object* v_traceArgs_8005_, lean_object* v_libFile_8006_, uint8_t v_linkDeps_8007_, lean_object* v_libName_8008_, uint8_t v_plugin_8009_, lean_object* v_libs_8010_, lean_object* v___y_8011_, lean_object* v___y_8012_, lean_object* v___y_8013_, lean_object* v___y_8014_, lean_object* v___y_8015_, lean_object* v___y_8016_){
_start:
{
lean_object* v_log_8018_; uint8_t v_action_8019_; uint8_t v_wantsRebuild_8020_; lean_object* v_trace_8021_; lean_object* v_buildTime_8022_; lean_object* v___x_8024_; uint8_t v_isShared_8025_; uint8_t v_isSharedCheck_8082_; 
v_log_8018_ = lean_ctor_get(v___y_8016_, 0);
v_action_8019_ = lean_ctor_get_uint8(v___y_8016_, sizeof(void*)*3);
v_wantsRebuild_8020_ = lean_ctor_get_uint8(v___y_8016_, sizeof(void*)*3 + 1);
v_trace_8021_ = lean_ctor_get(v___y_8016_, 1);
v_buildTime_8022_ = lean_ctor_get(v___y_8016_, 2);
v_isSharedCheck_8082_ = !lean_is_exclusive(v___y_8016_);
if (v_isSharedCheck_8082_ == 0)
{
v___x_8024_ = v___y_8016_;
v_isShared_8025_ = v_isSharedCheck_8082_;
goto v_resetjp_8023_;
}
else
{
lean_inc(v_buildTime_8022_);
lean_inc(v_trace_8021_);
lean_inc(v_log_8018_);
lean_dec(v___y_8016_);
v___x_8024_ = lean_box(0);
v_isShared_8025_ = v_isSharedCheck_8082_;
goto v_resetjp_8023_;
}
v_resetjp_8023_:
{
lean_object* v_leanTrace_8026_; lean_object* v___x_8027_; lean_object* v___f_8028_; lean_object* v___x_8029_; uint64_t v___y_8031_; uint64_t v___x_8071_; lean_object* v___x_8072_; lean_object* v___x_8073_; uint8_t v___x_8074_; 
v_leanTrace_8026_ = lean_ctor_get(v___y_8015_, 2);
v___x_8027_ = lean_box(v_linkDeps_8007_);
lean_inc_ref(v_libs_8010_);
lean_inc_ref(v_libFile_8006_);
lean_inc_ref(v_traceArgs_8005_);
v___f_8028_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8028_, 0, v_objs_8003_);
lean_closure_set(v___f_8028_, 1, v_weakArgs_8004_);
lean_closure_set(v___f_8028_, 2, v_traceArgs_8005_);
lean_closure_set(v___f_8028_, 3, v_libFile_8006_);
lean_closure_set(v___f_8028_, 4, v___x_8027_);
lean_closure_set(v___f_8028_, 5, v_libs_8010_);
lean_inc_ref(v_leanTrace_8026_);
v___x_8029_ = l_Lake_BuildTrace_mix(v_trace_8021_, v_leanTrace_8026_);
v___x_8071_ = l_Lake_Hash_nil;
v___x_8072_ = lean_unsigned_to_nat(0u);
v___x_8073_ = lean_array_get_size(v_traceArgs_8005_);
v___x_8074_ = lean_nat_dec_lt(v___x_8072_, v___x_8073_);
if (v___x_8074_ == 0)
{
v___y_8031_ = v___x_8071_;
goto v___jp_8030_;
}
else
{
uint8_t v___x_8075_; 
v___x_8075_ = lean_nat_dec_le(v___x_8073_, v___x_8073_);
if (v___x_8075_ == 0)
{
if (v___x_8074_ == 0)
{
v___y_8031_ = v___x_8071_;
goto v___jp_8030_;
}
else
{
size_t v___x_8076_; size_t v___x_8077_; uint64_t v___x_8078_; 
v___x_8076_ = ((size_t)0ULL);
v___x_8077_ = lean_usize_of_nat(v___x_8073_);
v___x_8078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8005_, v___x_8076_, v___x_8077_, v___x_8071_);
v___y_8031_ = v___x_8078_;
goto v___jp_8030_;
}
}
else
{
size_t v___x_8079_; size_t v___x_8080_; uint64_t v___x_8081_; 
v___x_8079_ = ((size_t)0ULL);
v___x_8080_ = lean_usize_of_nat(v___x_8073_);
v___x_8081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8005_, v___x_8079_, v___x_8080_, v___x_8071_);
v___y_8031_ = v___x_8081_;
goto v___jp_8030_;
}
}
v___jp_8030_:
{
lean_object* v___x_8032_; lean_object* v___x_8033_; lean_object* v___x_8034_; lean_object* v___x_8035_; lean_object* v___x_8036_; lean_object* v___x_8037_; lean_object* v___x_8038_; lean_object* v___x_8039_; lean_object* v___x_8040_; lean_object* v___x_8041_; lean_object* v___x_8042_; lean_object* v___x_8043_; lean_object* v___x_8045_; 
v___x_8032_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8033_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8034_ = lean_array_to_list(v_traceArgs_8005_);
v___x_8035_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8034_);
lean_dec(v___x_8034_);
v___x_8036_ = lean_string_append(v___x_8033_, v___x_8035_);
lean_dec_ref(v___x_8035_);
v___x_8037_ = lean_string_append(v___x_8032_, v___x_8036_);
lean_dec_ref(v___x_8036_);
v___x_8038_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8039_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8040_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8040_, 0, v___x_8037_);
lean_ctor_set(v___x_8040_, 1, v___x_8038_);
lean_ctor_set(v___x_8040_, 2, v___x_8039_);
lean_ctor_set_uint64(v___x_8040_, sizeof(void*)*3, v___y_8031_);
v___x_8041_ = l_Lake_BuildTrace_mix(v___x_8029_, v___x_8040_);
v___x_8042_ = l_Lake_platformTrace;
v___x_8043_ = l_Lake_BuildTrace_mix(v___x_8041_, v___x_8042_);
if (v_isShared_8025_ == 0)
{
lean_ctor_set(v___x_8024_, 1, v___x_8043_);
v___x_8045_ = v___x_8024_;
goto v_reusejp_8044_;
}
else
{
lean_object* v_reuseFailAlloc_8070_; 
v_reuseFailAlloc_8070_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8070_, 0, v_log_8018_);
lean_ctor_set(v_reuseFailAlloc_8070_, 1, v___x_8043_);
lean_ctor_set(v_reuseFailAlloc_8070_, 2, v_buildTime_8022_);
lean_ctor_set_uint8(v_reuseFailAlloc_8070_, sizeof(void*)*3, v_action_8019_);
lean_ctor_set_uint8(v_reuseFailAlloc_8070_, sizeof(void*)*3 + 1, v_wantsRebuild_8020_);
v___x_8045_ = v_reuseFailAlloc_8070_;
goto v_reusejp_8044_;
}
v_reusejp_8044_:
{
uint8_t v___x_8046_; lean_object* v___x_8047_; uint8_t v___x_8048_; lean_object* v___x_8049_; 
v___x_8046_ = 0;
v___x_8047_ = l_Lake_sharedLibExt;
v___x_8048_ = 1;
v___x_8049_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8006_, v___f_8028_, v___x_8046_, v___x_8047_, v___x_8048_, v___x_8046_, v___x_8046_, v___y_8011_, v___y_8012_, v___y_8013_, v___y_8014_, v___y_8015_, v___x_8045_);
if (lean_obj_tag(v___x_8049_) == 0)
{
lean_object* v_a_8050_; lean_object* v_a_8051_; lean_object* v___x_8053_; uint8_t v_isShared_8054_; uint8_t v_isSharedCheck_8060_; 
v_a_8050_ = lean_ctor_get(v___x_8049_, 0);
v_a_8051_ = lean_ctor_get(v___x_8049_, 1);
v_isSharedCheck_8060_ = !lean_is_exclusive(v___x_8049_);
if (v_isSharedCheck_8060_ == 0)
{
v___x_8053_ = v___x_8049_;
v_isShared_8054_ = v_isSharedCheck_8060_;
goto v_resetjp_8052_;
}
else
{
lean_inc(v_a_8051_);
lean_inc(v_a_8050_);
lean_dec(v___x_8049_);
v___x_8053_ = lean_box(0);
v_isShared_8054_ = v_isSharedCheck_8060_;
goto v_resetjp_8052_;
}
v_resetjp_8052_:
{
lean_object* v_path_8055_; lean_object* v___x_8056_; lean_object* v___x_8058_; 
v_path_8055_ = lean_ctor_get(v_a_8050_, 1);
lean_inc_ref(v_path_8055_);
lean_dec(v_a_8050_);
v___x_8056_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_8056_, 0, v_path_8055_);
lean_ctor_set(v___x_8056_, 1, v_libName_8008_);
lean_ctor_set(v___x_8056_, 2, v_libs_8010_);
lean_ctor_set_uint8(v___x_8056_, sizeof(void*)*3, v_plugin_8009_);
if (v_isShared_8054_ == 0)
{
lean_ctor_set(v___x_8053_, 0, v___x_8056_);
v___x_8058_ = v___x_8053_;
goto v_reusejp_8057_;
}
else
{
lean_object* v_reuseFailAlloc_8059_; 
v_reuseFailAlloc_8059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8059_, 0, v___x_8056_);
lean_ctor_set(v_reuseFailAlloc_8059_, 1, v_a_8051_);
v___x_8058_ = v_reuseFailAlloc_8059_;
goto v_reusejp_8057_;
}
v_reusejp_8057_:
{
return v___x_8058_;
}
}
}
else
{
lean_object* v_a_8061_; lean_object* v_a_8062_; lean_object* v___x_8064_; uint8_t v_isShared_8065_; uint8_t v_isSharedCheck_8069_; 
lean_dec_ref(v_libs_8010_);
lean_dec_ref(v_libName_8008_);
v_a_8061_ = lean_ctor_get(v___x_8049_, 0);
v_a_8062_ = lean_ctor_get(v___x_8049_, 1);
v_isSharedCheck_8069_ = !lean_is_exclusive(v___x_8049_);
if (v_isSharedCheck_8069_ == 0)
{
v___x_8064_ = v___x_8049_;
v_isShared_8065_ = v_isSharedCheck_8069_;
goto v_resetjp_8063_;
}
else
{
lean_inc(v_a_8062_);
lean_inc(v_a_8061_);
lean_dec(v___x_8049_);
v___x_8064_ = lean_box(0);
v_isShared_8065_ = v_isSharedCheck_8069_;
goto v_resetjp_8063_;
}
v_resetjp_8063_:
{
lean_object* v___x_8067_; 
if (v_isShared_8065_ == 0)
{
v___x_8067_ = v___x_8064_;
goto v_reusejp_8066_;
}
else
{
lean_object* v_reuseFailAlloc_8068_; 
v_reuseFailAlloc_8068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8068_, 0, v_a_8061_);
lean_ctor_set(v_reuseFailAlloc_8068_, 1, v_a_8062_);
v___x_8067_ = v_reuseFailAlloc_8068_;
goto v_reusejp_8066_;
}
v_reusejp_8066_:
{
return v___x_8067_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_8083_, lean_object* v_weakArgs_8084_, lean_object* v_traceArgs_8085_, lean_object* v_libFile_8086_, lean_object* v_linkDeps_8087_, lean_object* v_libName_8088_, lean_object* v_plugin_8089_, lean_object* v_libs_8090_, lean_object* v___y_8091_, lean_object* v___y_8092_, lean_object* v___y_8093_, lean_object* v___y_8094_, lean_object* v___y_8095_, lean_object* v___y_8096_, lean_object* v___y_8097_){
_start:
{
uint8_t v_linkDeps_boxed_8098_; uint8_t v_plugin_boxed_8099_; lean_object* v_res_8100_; 
v_linkDeps_boxed_8098_ = lean_unbox(v_linkDeps_8087_);
v_plugin_boxed_8099_ = lean_unbox(v_plugin_8089_);
v_res_8100_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_8083_, v_weakArgs_8084_, v_traceArgs_8085_, v_libFile_8086_, v_linkDeps_boxed_8098_, v_libName_8088_, v_plugin_boxed_8099_, v_libs_8090_, v___y_8091_, v___y_8092_, v___y_8093_, v___y_8094_, v___y_8095_, v___y_8096_);
lean_dec_ref(v___y_8095_);
lean_dec(v___y_8094_);
lean_dec(v___y_8093_);
lean_dec(v___y_8092_);
return v_res_8100_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_8101_, lean_object* v_traceArgs_8102_, lean_object* v_libFile_8103_, uint8_t v_linkDeps_8104_, lean_object* v_libName_8105_, uint8_t v_plugin_8106_, lean_object* v_linkLibs_8107_, lean_object* v___x_8108_, lean_object* v_objs_8109_, lean_object* v___y_8110_, lean_object* v___y_8111_, lean_object* v___y_8112_, lean_object* v___y_8113_, lean_object* v___y_8114_, lean_object* v___y_8115_){
_start:
{
lean_object* v_trace_8117_; lean_object* v___x_8118_; lean_object* v___x_8119_; lean_object* v___f_8120_; lean_object* v___x_8121_; lean_object* v___x_8122_; lean_object* v___x_8123_; uint8_t v___x_8124_; lean_object* v___x_8125_; lean_object* v___x_8126_; 
v_trace_8117_ = lean_ctor_get(v___y_8115_, 1);
v___x_8118_ = lean_box(v_linkDeps_8104_);
v___x_8119_ = lean_box(v_plugin_8106_);
v___f_8120_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_8120_, 0, v_objs_8109_);
lean_closure_set(v___f_8120_, 1, v_weakArgs_8101_);
lean_closure_set(v___f_8120_, 2, v_traceArgs_8102_);
lean_closure_set(v___f_8120_, 3, v_libFile_8103_);
lean_closure_set(v___f_8120_, 4, v___x_8118_);
lean_closure_set(v___f_8120_, 5, v_libName_8105_);
lean_closure_set(v___f_8120_, 6, v___x_8119_);
v___x_8121_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8122_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8107_, v___x_8121_);
v___x_8123_ = lean_unsigned_to_nat(0u);
v___x_8124_ = 0;
v___x_8125_ = l_Lake_Job_mapM___redArg(v___x_8108_, v___x_8122_, v___f_8120_, v___x_8123_, v___x_8124_, v___y_8110_, v___y_8111_, v___y_8112_, v___y_8113_, v___y_8114_, v_trace_8117_);
v___x_8126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8126_, 0, v___x_8125_);
lean_ctor_set(v___x_8126_, 1, v___y_8115_);
return v___x_8126_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_8127_, lean_object* v_traceArgs_8128_, lean_object* v_libFile_8129_, lean_object* v_linkDeps_8130_, lean_object* v_libName_8131_, lean_object* v_plugin_8132_, lean_object* v_linkLibs_8133_, lean_object* v___x_8134_, lean_object* v_objs_8135_, lean_object* v___y_8136_, lean_object* v___y_8137_, lean_object* v___y_8138_, lean_object* v___y_8139_, lean_object* v___y_8140_, lean_object* v___y_8141_, lean_object* v___y_8142_){
_start:
{
uint8_t v_linkDeps_boxed_8143_; uint8_t v_plugin_boxed_8144_; lean_object* v_res_8145_; 
v_linkDeps_boxed_8143_ = lean_unbox(v_linkDeps_8130_);
v_plugin_boxed_8144_ = lean_unbox(v_plugin_8132_);
v_res_8145_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_8127_, v_traceArgs_8128_, v_libFile_8129_, v_linkDeps_boxed_8143_, v_libName_8131_, v_plugin_boxed_8144_, v_linkLibs_8133_, v___x_8134_, v_objs_8135_, v___y_8136_, v___y_8137_, v___y_8138_, v___y_8139_, v___y_8140_, v___y_8141_);
lean_dec_ref(v___y_8140_);
lean_dec(v___y_8139_);
lean_dec(v___y_8138_);
lean_dec(v___y_8137_);
lean_dec_ref(v_linkLibs_8133_);
return v_res_8145_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8146_, lean_object* v_libFile_8147_, lean_object* v_linkObjs_8148_, lean_object* v_linkLibs_8149_, lean_object* v_weakArgs_8150_, lean_object* v_traceArgs_8151_, uint8_t v_plugin_8152_, uint8_t v_linkDeps_8153_, lean_object* v_a_8154_, lean_object* v_a_8155_, lean_object* v_a_8156_, lean_object* v_a_8157_, lean_object* v_a_8158_, lean_object* v_a_8159_){
_start:
{
lean_object* v___x_8161_; lean_object* v___x_8162_; lean_object* v___x_8163_; lean_object* v___f_8164_; lean_object* v___x_8165_; lean_object* v___x_8166_; lean_object* v___x_8167_; uint8_t v___x_8168_; lean_object* v___x_8169_; 
v___x_8161_ = l_Lake_instDataKindDynlib;
v___x_8162_ = lean_box(v_linkDeps_8153_);
v___x_8163_ = lean_box(v_plugin_8152_);
v___f_8164_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_8164_, 0, v_weakArgs_8150_);
lean_closure_set(v___f_8164_, 1, v_traceArgs_8151_);
lean_closure_set(v___f_8164_, 2, v_libFile_8147_);
lean_closure_set(v___f_8164_, 3, v___x_8162_);
lean_closure_set(v___f_8164_, 4, v_libName_8146_);
lean_closure_set(v___f_8164_, 5, v___x_8163_);
lean_closure_set(v___f_8164_, 6, v_linkLibs_8149_);
lean_closure_set(v___f_8164_, 7, v___x_8161_);
v___x_8165_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8166_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8148_, v___x_8165_);
v___x_8167_ = lean_unsigned_to_nat(0u);
v___x_8168_ = 1;
v___x_8169_ = l_Lake_Job_bindM___redArg(v___x_8161_, v___x_8166_, v___f_8164_, v___x_8167_, v___x_8168_, v_a_8154_, v_a_8155_, v_a_8156_, v_a_8157_, v_a_8158_, v_a_8159_);
return v___x_8169_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8170_, lean_object* v_libFile_8171_, lean_object* v_linkObjs_8172_, lean_object* v_linkLibs_8173_, lean_object* v_weakArgs_8174_, lean_object* v_traceArgs_8175_, lean_object* v_plugin_8176_, lean_object* v_linkDeps_8177_, lean_object* v_a_8178_, lean_object* v_a_8179_, lean_object* v_a_8180_, lean_object* v_a_8181_, lean_object* v_a_8182_, lean_object* v_a_8183_, lean_object* v_a_8184_){
_start:
{
uint8_t v_plugin_boxed_8185_; uint8_t v_linkDeps_boxed_8186_; lean_object* v_res_8187_; 
v_plugin_boxed_8185_ = lean_unbox(v_plugin_8176_);
v_linkDeps_boxed_8186_ = lean_unbox(v_linkDeps_8177_);
v_res_8187_ = l_Lake_buildLeanSharedLib(v_libName_8170_, v_libFile_8171_, v_linkObjs_8172_, v_linkLibs_8173_, v_weakArgs_8174_, v_traceArgs_8175_, v_plugin_boxed_8185_, v_linkDeps_boxed_8186_, v_a_8178_, v_a_8179_, v_a_8180_, v_a_8181_, v_a_8182_, v_a_8183_);
lean_dec_ref(v_a_8183_);
lean_dec_ref(v_a_8182_);
lean_dec(v_a_8181_);
lean_dec(v_a_8180_);
lean_dec(v_a_8179_);
lean_dec_ref(v_linkObjs_8172_);
return v_res_8187_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_8188_, lean_object* v_objs_8189_, lean_object* v_weakArgs_8190_, lean_object* v_traceArgs_8191_, uint8_t v_sharedLean_8192_, lean_object* v_exeFile_8193_, lean_object* v___y_8194_, lean_object* v___y_8195_, lean_object* v___y_8196_, lean_object* v___y_8197_, lean_object* v___y_8198_, lean_object* v___y_8199_){
_start:
{
lean_object* v___x_8201_; 
v___x_8201_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_8188_, v___y_8199_);
if (lean_obj_tag(v___x_8201_) == 0)
{
lean_object* v_toContext_8202_; lean_object* v_lakeEnv_8203_; lean_object* v_lean_8204_; lean_object* v_a_8205_; lean_object* v_a_8206_; lean_object* v_leanLibDir_8207_; lean_object* v_cc_8208_; lean_object* v_log_8209_; uint8_t v_action_8210_; uint8_t v_wantsRebuild_8211_; lean_object* v_trace_8212_; lean_object* v_buildTime_8213_; lean_object* v___x_8215_; uint8_t v_isShared_8216_; uint8_t v_isSharedCheck_8252_; 
v_toContext_8202_ = lean_ctor_get(v___y_8198_, 1);
v_lakeEnv_8203_ = lean_ctor_get(v_toContext_8202_, 0);
v_lean_8204_ = lean_ctor_get(v_lakeEnv_8203_, 1);
v_a_8205_ = lean_ctor_get(v___x_8201_, 1);
lean_inc(v_a_8205_);
v_a_8206_ = lean_ctor_get(v___x_8201_, 0);
lean_inc(v_a_8206_);
lean_dec_ref_known(v___x_8201_, 2);
v_leanLibDir_8207_ = lean_ctor_get(v_lean_8204_, 3);
v_cc_8208_ = lean_ctor_get(v_lean_8204_, 14);
v_log_8209_ = lean_ctor_get(v_a_8205_, 0);
v_action_8210_ = lean_ctor_get_uint8(v_a_8205_, sizeof(void*)*3);
v_wantsRebuild_8211_ = lean_ctor_get_uint8(v_a_8205_, sizeof(void*)*3 + 1);
v_trace_8212_ = lean_ctor_get(v_a_8205_, 1);
v_buildTime_8213_ = lean_ctor_get(v_a_8205_, 2);
v_isSharedCheck_8252_ = !lean_is_exclusive(v_a_8205_);
if (v_isSharedCheck_8252_ == 0)
{
v___x_8215_ = v_a_8205_;
v_isShared_8216_ = v_isSharedCheck_8252_;
goto v_resetjp_8214_;
}
else
{
lean_inc(v_buildTime_8213_);
lean_inc(v_trace_8212_);
lean_inc(v_log_8209_);
lean_dec(v_a_8205_);
v___x_8215_ = lean_box(0);
v_isShared_8216_ = v_isSharedCheck_8252_;
goto v_resetjp_8214_;
}
v_resetjp_8214_:
{
lean_object* v___x_8217_; lean_object* v___x_8218_; lean_object* v___x_8219_; lean_object* v___x_8220_; lean_object* v___x_8221_; lean_object* v___x_8222_; lean_object* v___x_8223_; lean_object* v___x_8224_; lean_object* v___x_8225_; lean_object* v___x_8226_; lean_object* v___x_8227_; 
v___x_8217_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_8189_, v_a_8206_);
lean_dec(v_a_8206_);
v___x_8218_ = l_Array_append___redArg(v___x_8217_, v_weakArgs_8190_);
v___x_8219_ = l_Array_append___redArg(v___x_8218_, v_traceArgs_8191_);
v___x_8220_ = lean_unsigned_to_nat(2u);
v___x_8221_ = lean_mk_empty_array_with_capacity(v___x_8220_);
lean_dec_ref(v___x_8221_);
v___x_8222_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_8207_);
v___x_8223_ = lean_array_push(v___x_8222_, v_leanLibDir_8207_);
v___x_8224_ = l_Array_append___redArg(v___x_8219_, v___x_8223_);
lean_dec_ref(v___x_8223_);
v___x_8225_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8192_, v_lean_8204_);
v___x_8226_ = l_Array_append___redArg(v___x_8224_, v___x_8225_);
lean_dec_ref(v___x_8225_);
lean_inc_ref(v_cc_8208_);
v___x_8227_ = l_Lake_compileExe(v_exeFile_8193_, v___x_8226_, v_cc_8208_, v_log_8209_);
lean_dec_ref(v___x_8226_);
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
lean_object* v___x_8234_; 
if (v_isShared_8216_ == 0)
{
lean_ctor_set(v___x_8215_, 0, v_a_8229_);
v___x_8234_ = v___x_8215_;
goto v_reusejp_8233_;
}
else
{
lean_object* v_reuseFailAlloc_8238_; 
v_reuseFailAlloc_8238_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8238_, 0, v_a_8229_);
lean_ctor_set(v_reuseFailAlloc_8238_, 1, v_trace_8212_);
lean_ctor_set(v_reuseFailAlloc_8238_, 2, v_buildTime_8213_);
lean_ctor_set_uint8(v_reuseFailAlloc_8238_, sizeof(void*)*3, v_action_8210_);
lean_ctor_set_uint8(v_reuseFailAlloc_8238_, sizeof(void*)*3 + 1, v_wantsRebuild_8211_);
v___x_8234_ = v_reuseFailAlloc_8238_;
goto v_reusejp_8233_;
}
v_reusejp_8233_:
{
lean_object* v___x_8236_; 
if (v_isShared_8232_ == 0)
{
lean_ctor_set(v___x_8231_, 1, v___x_8234_);
v___x_8236_ = v___x_8231_;
goto v_reusejp_8235_;
}
else
{
lean_object* v_reuseFailAlloc_8237_; 
v_reuseFailAlloc_8237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8237_, 0, v_a_8228_);
lean_ctor_set(v_reuseFailAlloc_8237_, 1, v___x_8234_);
v___x_8236_ = v_reuseFailAlloc_8237_;
goto v_reusejp_8235_;
}
v_reusejp_8235_:
{
return v___x_8236_;
}
}
}
}
else
{
lean_object* v_a_8240_; lean_object* v_a_8241_; lean_object* v___x_8243_; uint8_t v_isShared_8244_; uint8_t v_isSharedCheck_8251_; 
v_a_8240_ = lean_ctor_get(v___x_8227_, 0);
v_a_8241_ = lean_ctor_get(v___x_8227_, 1);
v_isSharedCheck_8251_ = !lean_is_exclusive(v___x_8227_);
if (v_isSharedCheck_8251_ == 0)
{
v___x_8243_ = v___x_8227_;
v_isShared_8244_ = v_isSharedCheck_8251_;
goto v_resetjp_8242_;
}
else
{
lean_inc(v_a_8241_);
lean_inc(v_a_8240_);
lean_dec(v___x_8227_);
v___x_8243_ = lean_box(0);
v_isShared_8244_ = v_isSharedCheck_8251_;
goto v_resetjp_8242_;
}
v_resetjp_8242_:
{
lean_object* v___x_8246_; 
if (v_isShared_8216_ == 0)
{
lean_ctor_set(v___x_8215_, 0, v_a_8241_);
v___x_8246_ = v___x_8215_;
goto v_reusejp_8245_;
}
else
{
lean_object* v_reuseFailAlloc_8250_; 
v_reuseFailAlloc_8250_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8250_, 0, v_a_8241_);
lean_ctor_set(v_reuseFailAlloc_8250_, 1, v_trace_8212_);
lean_ctor_set(v_reuseFailAlloc_8250_, 2, v_buildTime_8213_);
lean_ctor_set_uint8(v_reuseFailAlloc_8250_, sizeof(void*)*3, v_action_8210_);
lean_ctor_set_uint8(v_reuseFailAlloc_8250_, sizeof(void*)*3 + 1, v_wantsRebuild_8211_);
v___x_8246_ = v_reuseFailAlloc_8250_;
goto v_reusejp_8245_;
}
v_reusejp_8245_:
{
lean_object* v___x_8248_; 
if (v_isShared_8244_ == 0)
{
lean_ctor_set(v___x_8243_, 1, v___x_8246_);
v___x_8248_ = v___x_8243_;
goto v_reusejp_8247_;
}
else
{
lean_object* v_reuseFailAlloc_8249_; 
v_reuseFailAlloc_8249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8249_, 0, v_a_8240_);
lean_ctor_set(v_reuseFailAlloc_8249_, 1, v___x_8246_);
v___x_8248_ = v_reuseFailAlloc_8249_;
goto v_reusejp_8247_;
}
v_reusejp_8247_:
{
return v___x_8248_;
}
}
}
}
}
}
else
{
lean_object* v_a_8253_; lean_object* v_a_8254_; lean_object* v___x_8256_; uint8_t v_isShared_8257_; uint8_t v_isSharedCheck_8261_; 
lean_dec_ref(v_exeFile_8193_);
v_a_8253_ = lean_ctor_get(v___x_8201_, 0);
v_a_8254_ = lean_ctor_get(v___x_8201_, 1);
v_isSharedCheck_8261_ = !lean_is_exclusive(v___x_8201_);
if (v_isSharedCheck_8261_ == 0)
{
v___x_8256_ = v___x_8201_;
v_isShared_8257_ = v_isSharedCheck_8261_;
goto v_resetjp_8255_;
}
else
{
lean_inc(v_a_8254_);
lean_inc(v_a_8253_);
lean_dec(v___x_8201_);
v___x_8256_ = lean_box(0);
v_isShared_8257_ = v_isSharedCheck_8261_;
goto v_resetjp_8255_;
}
v_resetjp_8255_:
{
lean_object* v___x_8259_; 
if (v_isShared_8257_ == 0)
{
v___x_8259_ = v___x_8256_;
goto v_reusejp_8258_;
}
else
{
lean_object* v_reuseFailAlloc_8260_; 
v_reuseFailAlloc_8260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8260_, 0, v_a_8253_);
lean_ctor_set(v_reuseFailAlloc_8260_, 1, v_a_8254_);
v___x_8259_ = v_reuseFailAlloc_8260_;
goto v_reusejp_8258_;
}
v_reusejp_8258_:
{
return v___x_8259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8262_, lean_object* v_objs_8263_, lean_object* v_weakArgs_8264_, lean_object* v_traceArgs_8265_, lean_object* v_sharedLean_8266_, lean_object* v_exeFile_8267_, lean_object* v___y_8268_, lean_object* v___y_8269_, lean_object* v___y_8270_, lean_object* v___y_8271_, lean_object* v___y_8272_, lean_object* v___y_8273_, lean_object* v___y_8274_){
_start:
{
uint8_t v_sharedLean_boxed_8275_; lean_object* v_res_8276_; 
v_sharedLean_boxed_8275_ = lean_unbox(v_sharedLean_8266_);
v_res_8276_ = l_Lake_buildLeanExe___lam__0(v_libs_8262_, v_objs_8263_, v_weakArgs_8264_, v_traceArgs_8265_, v_sharedLean_boxed_8275_, v_exeFile_8267_, v___y_8268_, v___y_8269_, v___y_8270_, v___y_8271_, v___y_8272_, v___y_8273_);
lean_dec_ref(v___y_8272_);
lean_dec(v___y_8271_);
lean_dec(v___y_8270_);
lean_dec(v___y_8269_);
lean_dec_ref(v___y_8268_);
lean_dec_ref(v_traceArgs_8265_);
lean_dec_ref(v_weakArgs_8264_);
lean_dec_ref(v_objs_8263_);
lean_dec_ref(v_libs_8262_);
return v_res_8276_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8277_, lean_object* v_weakArgs_8278_, lean_object* v_traceArgs_8279_, uint8_t v_sharedLean_8280_, lean_object* v_exeFile_8281_, lean_object* v_libs_8282_, lean_object* v___y_8283_, lean_object* v___y_8284_, lean_object* v___y_8285_, lean_object* v___y_8286_, lean_object* v___y_8287_, lean_object* v___y_8288_){
_start:
{
lean_object* v_log_8290_; uint8_t v_action_8291_; uint8_t v_wantsRebuild_8292_; lean_object* v_trace_8293_; lean_object* v_buildTime_8294_; lean_object* v___x_8296_; uint8_t v_isShared_8297_; uint8_t v_isSharedCheck_8353_; 
v_log_8290_ = lean_ctor_get(v___y_8288_, 0);
v_action_8291_ = lean_ctor_get_uint8(v___y_8288_, sizeof(void*)*3);
v_wantsRebuild_8292_ = lean_ctor_get_uint8(v___y_8288_, sizeof(void*)*3 + 1);
v_trace_8293_ = lean_ctor_get(v___y_8288_, 1);
v_buildTime_8294_ = lean_ctor_get(v___y_8288_, 2);
v_isSharedCheck_8353_ = !lean_is_exclusive(v___y_8288_);
if (v_isSharedCheck_8353_ == 0)
{
v___x_8296_ = v___y_8288_;
v_isShared_8297_ = v_isSharedCheck_8353_;
goto v_resetjp_8295_;
}
else
{
lean_inc(v_buildTime_8294_);
lean_inc(v_trace_8293_);
lean_inc(v_log_8290_);
lean_dec(v___y_8288_);
v___x_8296_ = lean_box(0);
v_isShared_8297_ = v_isSharedCheck_8353_;
goto v_resetjp_8295_;
}
v_resetjp_8295_:
{
lean_object* v_leanTrace_8298_; lean_object* v___x_8299_; lean_object* v___f_8300_; lean_object* v___x_8301_; uint64_t v___y_8303_; uint64_t v___x_8342_; lean_object* v___x_8343_; lean_object* v___x_8344_; uint8_t v___x_8345_; 
v_leanTrace_8298_ = lean_ctor_get(v___y_8287_, 2);
v___x_8299_ = lean_box(v_sharedLean_8280_);
lean_inc_ref(v_exeFile_8281_);
lean_inc_ref(v_traceArgs_8279_);
v___f_8300_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8300_, 0, v_libs_8282_);
lean_closure_set(v___f_8300_, 1, v_objs_8277_);
lean_closure_set(v___f_8300_, 2, v_weakArgs_8278_);
lean_closure_set(v___f_8300_, 3, v_traceArgs_8279_);
lean_closure_set(v___f_8300_, 4, v___x_8299_);
lean_closure_set(v___f_8300_, 5, v_exeFile_8281_);
lean_inc_ref(v_leanTrace_8298_);
v___x_8301_ = l_Lake_BuildTrace_mix(v_trace_8293_, v_leanTrace_8298_);
v___x_8342_ = l_Lake_Hash_nil;
v___x_8343_ = lean_unsigned_to_nat(0u);
v___x_8344_ = lean_array_get_size(v_traceArgs_8279_);
v___x_8345_ = lean_nat_dec_lt(v___x_8343_, v___x_8344_);
if (v___x_8345_ == 0)
{
v___y_8303_ = v___x_8342_;
goto v___jp_8302_;
}
else
{
uint8_t v___x_8346_; 
v___x_8346_ = lean_nat_dec_le(v___x_8344_, v___x_8344_);
if (v___x_8346_ == 0)
{
if (v___x_8345_ == 0)
{
v___y_8303_ = v___x_8342_;
goto v___jp_8302_;
}
else
{
size_t v___x_8347_; size_t v___x_8348_; uint64_t v___x_8349_; 
v___x_8347_ = ((size_t)0ULL);
v___x_8348_ = lean_usize_of_nat(v___x_8344_);
v___x_8349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8279_, v___x_8347_, v___x_8348_, v___x_8342_);
v___y_8303_ = v___x_8349_;
goto v___jp_8302_;
}
}
else
{
size_t v___x_8350_; size_t v___x_8351_; uint64_t v___x_8352_; 
v___x_8350_ = ((size_t)0ULL);
v___x_8351_ = lean_usize_of_nat(v___x_8344_);
v___x_8352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8279_, v___x_8350_, v___x_8351_, v___x_8342_);
v___y_8303_ = v___x_8352_;
goto v___jp_8302_;
}
}
v___jp_8302_:
{
lean_object* v___x_8304_; lean_object* v___x_8305_; lean_object* v___x_8306_; lean_object* v___x_8307_; lean_object* v___x_8308_; lean_object* v___x_8309_; lean_object* v___x_8310_; lean_object* v___x_8311_; lean_object* v___x_8312_; lean_object* v___x_8313_; lean_object* v___x_8314_; lean_object* v___x_8315_; lean_object* v___x_8317_; 
v___x_8304_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8305_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8306_ = lean_array_to_list(v_traceArgs_8279_);
v___x_8307_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8306_);
lean_dec(v___x_8306_);
v___x_8308_ = lean_string_append(v___x_8305_, v___x_8307_);
lean_dec_ref(v___x_8307_);
v___x_8309_ = lean_string_append(v___x_8304_, v___x_8308_);
lean_dec_ref(v___x_8308_);
v___x_8310_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8311_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8312_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8312_, 0, v___x_8309_);
lean_ctor_set(v___x_8312_, 1, v___x_8310_);
lean_ctor_set(v___x_8312_, 2, v___x_8311_);
lean_ctor_set_uint64(v___x_8312_, sizeof(void*)*3, v___y_8303_);
v___x_8313_ = l_Lake_BuildTrace_mix(v___x_8301_, v___x_8312_);
v___x_8314_ = l_Lake_platformTrace;
v___x_8315_ = l_Lake_BuildTrace_mix(v___x_8313_, v___x_8314_);
if (v_isShared_8297_ == 0)
{
lean_ctor_set(v___x_8296_, 1, v___x_8315_);
v___x_8317_ = v___x_8296_;
goto v_reusejp_8316_;
}
else
{
lean_object* v_reuseFailAlloc_8341_; 
v_reuseFailAlloc_8341_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8341_, 0, v_log_8290_);
lean_ctor_set(v_reuseFailAlloc_8341_, 1, v___x_8315_);
lean_ctor_set(v_reuseFailAlloc_8341_, 2, v_buildTime_8294_);
lean_ctor_set_uint8(v_reuseFailAlloc_8341_, sizeof(void*)*3, v_action_8291_);
lean_ctor_set_uint8(v_reuseFailAlloc_8341_, sizeof(void*)*3 + 1, v_wantsRebuild_8292_);
v___x_8317_ = v_reuseFailAlloc_8341_;
goto v_reusejp_8316_;
}
v_reusejp_8316_:
{
uint8_t v___x_8318_; lean_object* v___x_8319_; uint8_t v___x_8320_; lean_object* v___x_8321_; 
v___x_8318_ = 0;
v___x_8319_ = l_System_FilePath_exeExtension;
v___x_8320_ = 1;
v___x_8321_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8281_, v___f_8300_, v___x_8318_, v___x_8319_, v___x_8320_, v___x_8320_, v___x_8318_, v___y_8283_, v___y_8284_, v___y_8285_, v___y_8286_, v___y_8287_, v___x_8317_);
if (lean_obj_tag(v___x_8321_) == 0)
{
lean_object* v_a_8322_; lean_object* v_a_8323_; lean_object* v___x_8325_; uint8_t v_isShared_8326_; uint8_t v_isSharedCheck_8331_; 
v_a_8322_ = lean_ctor_get(v___x_8321_, 0);
v_a_8323_ = lean_ctor_get(v___x_8321_, 1);
v_isSharedCheck_8331_ = !lean_is_exclusive(v___x_8321_);
if (v_isSharedCheck_8331_ == 0)
{
v___x_8325_ = v___x_8321_;
v_isShared_8326_ = v_isSharedCheck_8331_;
goto v_resetjp_8324_;
}
else
{
lean_inc(v_a_8323_);
lean_inc(v_a_8322_);
lean_dec(v___x_8321_);
v___x_8325_ = lean_box(0);
v_isShared_8326_ = v_isSharedCheck_8331_;
goto v_resetjp_8324_;
}
v_resetjp_8324_:
{
lean_object* v_path_8327_; lean_object* v___x_8329_; 
v_path_8327_ = lean_ctor_get(v_a_8322_, 1);
lean_inc_ref(v_path_8327_);
lean_dec(v_a_8322_);
if (v_isShared_8326_ == 0)
{
lean_ctor_set(v___x_8325_, 0, v_path_8327_);
v___x_8329_ = v___x_8325_;
goto v_reusejp_8328_;
}
else
{
lean_object* v_reuseFailAlloc_8330_; 
v_reuseFailAlloc_8330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8330_, 0, v_path_8327_);
lean_ctor_set(v_reuseFailAlloc_8330_, 1, v_a_8323_);
v___x_8329_ = v_reuseFailAlloc_8330_;
goto v_reusejp_8328_;
}
v_reusejp_8328_:
{
return v___x_8329_;
}
}
}
else
{
lean_object* v_a_8332_; lean_object* v_a_8333_; lean_object* v___x_8335_; uint8_t v_isShared_8336_; uint8_t v_isSharedCheck_8340_; 
v_a_8332_ = lean_ctor_get(v___x_8321_, 0);
v_a_8333_ = lean_ctor_get(v___x_8321_, 1);
v_isSharedCheck_8340_ = !lean_is_exclusive(v___x_8321_);
if (v_isSharedCheck_8340_ == 0)
{
v___x_8335_ = v___x_8321_;
v_isShared_8336_ = v_isSharedCheck_8340_;
goto v_resetjp_8334_;
}
else
{
lean_inc(v_a_8333_);
lean_inc(v_a_8332_);
lean_dec(v___x_8321_);
v___x_8335_ = lean_box(0);
v_isShared_8336_ = v_isSharedCheck_8340_;
goto v_resetjp_8334_;
}
v_resetjp_8334_:
{
lean_object* v___x_8338_; 
if (v_isShared_8336_ == 0)
{
v___x_8338_ = v___x_8335_;
goto v_reusejp_8337_;
}
else
{
lean_object* v_reuseFailAlloc_8339_; 
v_reuseFailAlloc_8339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8339_, 0, v_a_8332_);
lean_ctor_set(v_reuseFailAlloc_8339_, 1, v_a_8333_);
v___x_8338_ = v_reuseFailAlloc_8339_;
goto v_reusejp_8337_;
}
v_reusejp_8337_:
{
return v___x_8338_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8354_, lean_object* v_weakArgs_8355_, lean_object* v_traceArgs_8356_, lean_object* v_sharedLean_8357_, lean_object* v_exeFile_8358_, lean_object* v_libs_8359_, lean_object* v___y_8360_, lean_object* v___y_8361_, lean_object* v___y_8362_, lean_object* v___y_8363_, lean_object* v___y_8364_, lean_object* v___y_8365_, lean_object* v___y_8366_){
_start:
{
uint8_t v_sharedLean_boxed_8367_; lean_object* v_res_8368_; 
v_sharedLean_boxed_8367_ = lean_unbox(v_sharedLean_8357_);
v_res_8368_ = l_Lake_buildLeanExe___lam__1(v_objs_8354_, v_weakArgs_8355_, v_traceArgs_8356_, v_sharedLean_boxed_8367_, v_exeFile_8358_, v_libs_8359_, v___y_8360_, v___y_8361_, v___y_8362_, v___y_8363_, v___y_8364_, v___y_8365_);
lean_dec_ref(v___y_8364_);
lean_dec(v___y_8363_);
lean_dec(v___y_8362_);
lean_dec(v___y_8361_);
return v_res_8368_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8369_, lean_object* v_traceArgs_8370_, uint8_t v_sharedLean_8371_, lean_object* v_exeFile_8372_, lean_object* v_linkLibs_8373_, lean_object* v___x_8374_, lean_object* v_objs_8375_, lean_object* v___y_8376_, lean_object* v___y_8377_, lean_object* v___y_8378_, lean_object* v___y_8379_, lean_object* v___y_8380_, lean_object* v___y_8381_){
_start:
{
lean_object* v_trace_8383_; lean_object* v___x_8384_; lean_object* v___f_8385_; lean_object* v___x_8386_; lean_object* v___x_8387_; lean_object* v___x_8388_; uint8_t v___x_8389_; lean_object* v___x_8390_; lean_object* v___x_8391_; 
v_trace_8383_ = lean_ctor_get(v___y_8381_, 1);
v___x_8384_ = lean_box(v_sharedLean_8371_);
v___f_8385_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8385_, 0, v_objs_8375_);
lean_closure_set(v___f_8385_, 1, v_weakArgs_8369_);
lean_closure_set(v___f_8385_, 2, v_traceArgs_8370_);
lean_closure_set(v___f_8385_, 3, v___x_8384_);
lean_closure_set(v___f_8385_, 4, v_exeFile_8372_);
v___x_8386_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8387_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8373_, v___x_8386_);
v___x_8388_ = lean_unsigned_to_nat(0u);
v___x_8389_ = 0;
v___x_8390_ = l_Lake_Job_mapM___redArg(v___x_8374_, v___x_8387_, v___f_8385_, v___x_8388_, v___x_8389_, v___y_8376_, v___y_8377_, v___y_8378_, v___y_8379_, v___y_8380_, v_trace_8383_);
v___x_8391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8391_, 0, v___x_8390_);
lean_ctor_set(v___x_8391_, 1, v___y_8381_);
return v___x_8391_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8392_, lean_object* v_traceArgs_8393_, lean_object* v_sharedLean_8394_, lean_object* v_exeFile_8395_, lean_object* v_linkLibs_8396_, lean_object* v___x_8397_, lean_object* v_objs_8398_, lean_object* v___y_8399_, lean_object* v___y_8400_, lean_object* v___y_8401_, lean_object* v___y_8402_, lean_object* v___y_8403_, lean_object* v___y_8404_, lean_object* v___y_8405_){
_start:
{
uint8_t v_sharedLean_boxed_8406_; lean_object* v_res_8407_; 
v_sharedLean_boxed_8406_ = lean_unbox(v_sharedLean_8394_);
v_res_8407_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8392_, v_traceArgs_8393_, v_sharedLean_boxed_8406_, v_exeFile_8395_, v_linkLibs_8396_, v___x_8397_, v_objs_8398_, v___y_8399_, v___y_8400_, v___y_8401_, v___y_8402_, v___y_8403_, v___y_8404_);
lean_dec_ref(v___y_8403_);
lean_dec(v___y_8402_);
lean_dec(v___y_8401_);
lean_dec(v___y_8400_);
lean_dec_ref(v_linkLibs_8396_);
return v_res_8407_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8408_, lean_object* v_linkObjs_8409_, lean_object* v_linkLibs_8410_, lean_object* v_weakArgs_8411_, lean_object* v_traceArgs_8412_, uint8_t v_sharedLean_8413_, lean_object* v_a_8414_, lean_object* v_a_8415_, lean_object* v_a_8416_, lean_object* v_a_8417_, lean_object* v_a_8418_, lean_object* v_a_8419_){
_start:
{
lean_object* v___x_8421_; lean_object* v___x_8422_; lean_object* v___f_8423_; lean_object* v___x_8424_; lean_object* v___x_8425_; lean_object* v___x_8426_; uint8_t v___x_8427_; lean_object* v___x_8428_; 
v___x_8421_ = l_Lake_instDataKindFilePath;
v___x_8422_ = lean_box(v_sharedLean_8413_);
v___f_8423_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8423_, 0, v_weakArgs_8411_);
lean_closure_set(v___f_8423_, 1, v_traceArgs_8412_);
lean_closure_set(v___f_8423_, 2, v___x_8422_);
lean_closure_set(v___f_8423_, 3, v_exeFile_8408_);
lean_closure_set(v___f_8423_, 4, v_linkLibs_8410_);
lean_closure_set(v___f_8423_, 5, v___x_8421_);
v___x_8424_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8425_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8409_, v___x_8424_);
v___x_8426_ = lean_unsigned_to_nat(0u);
v___x_8427_ = 1;
v___x_8428_ = l_Lake_Job_bindM___redArg(v___x_8421_, v___x_8425_, v___f_8423_, v___x_8426_, v___x_8427_, v_a_8414_, v_a_8415_, v_a_8416_, v_a_8417_, v_a_8418_, v_a_8419_);
return v___x_8428_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8429_, lean_object* v_linkObjs_8430_, lean_object* v_linkLibs_8431_, lean_object* v_weakArgs_8432_, lean_object* v_traceArgs_8433_, lean_object* v_sharedLean_8434_, lean_object* v_a_8435_, lean_object* v_a_8436_, lean_object* v_a_8437_, lean_object* v_a_8438_, lean_object* v_a_8439_, lean_object* v_a_8440_, lean_object* v_a_8441_){
_start:
{
uint8_t v_sharedLean_boxed_8442_; lean_object* v_res_8443_; 
v_sharedLean_boxed_8442_ = lean_unbox(v_sharedLean_8434_);
v_res_8443_ = l_Lake_buildLeanExe(v_exeFile_8429_, v_linkObjs_8430_, v_linkLibs_8431_, v_weakArgs_8432_, v_traceArgs_8433_, v_sharedLean_boxed_8442_, v_a_8435_, v_a_8436_, v_a_8437_, v_a_8438_, v_a_8439_, v_a_8440_);
lean_dec_ref(v_a_8440_);
lean_dec_ref(v_a_8439_);
lean_dec(v_a_8438_);
lean_dec(v_a_8437_);
lean_dec(v_a_8436_);
lean_dec_ref(v_linkObjs_8430_);
return v_res_8443_;
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
