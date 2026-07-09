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
lean_object* v_toBuildConfig_2574_; uint8_t v_trustHash_2575_; lean_object* v___x_2576_; lean_object* v_hashFile_2577_; uint8_t v___y_2579_; uint8_t v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2617_; 
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
lean_ctor_set(v___x_2590_, 1, v___y_2581_);
lean_ctor_set(v___x_2590_, 2, v___y_2582_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3 + 1, v___y_2580_);
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
lean_ctor_set(v___x_2598_, 1, v___y_2581_);
lean_ctor_set(v___x_2598_, 2, v___y_2582_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3 + 1, v___y_2580_);
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
lean_ctor_set(v___x_2606_, 1, v___y_2581_);
lean_ctor_set(v___x_2606_, 2, v___y_2582_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 1, v___y_2580_);
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
lean_ctor_set(v___x_2614_, 1, v___y_2581_);
lean_ctor_set(v___x_2614_, 2, v___y_2582_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3 + 1, v___y_2580_);
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
v___y_2580_ = v_wantsRebuild_2620_;
v___y_2581_ = v_trace_2621_;
v___y_2582_ = v_buildTime_2622_;
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
v___y_2580_ = v_wantsRebuild_2626_;
v___y_2581_ = v_trace_2627_;
v___y_2582_ = v_buildTime_2628_;
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
uint8_t v___x_4347_; lean_object* v___x_4348_; 
lean_dec_ref_known(v___x_4346_, 1);
v___x_4347_ = 1;
v___x_4348_ = lean_io_hard_link(v_path_4324_, v_file_4303_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_dec_ref_known(v___x_4348_, 1);
if (v_exe_4305_ == 0)
{
v___y_4326_ = v___x_4345_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4349_, 0, v___x_4347_);
lean_ctor_set_uint8(v___x_4349_, 1, v___x_4322_);
lean_ctor_set_uint8(v___x_4349_, 2, v_exe_4305_);
lean_inc_ref_n(v___x_4349_, 2);
v___x_4350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v___x_4349_);
lean_ctor_set(v___x_4350_, 2, v___x_4349_);
v___x_4351_ = l_IO_setAccessRights(v_file_4303_, v___x_4350_);
lean_dec_ref_known(v___x_4350_, 3);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref_known(v___x_4351_, 1);
v___y_4326_ = v___x_4345_;
goto v___jp_4325_;
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = lean_io_error_to_string(v_a_4352_);
v___x_4354_ = 3;
v___x_4355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set_uint8(v___x_4355_, sizeof(void*)*1, v___x_4354_);
v___x_4356_ = lean_array_get_size(v___x_4345_);
v___x_4357_ = lean_array_push(v___x_4345_, v___x_4355_);
v___x_4358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4356_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
return v___x_4358_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v_a_4359_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4348_, 1);
v___x_4360_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4361_ = lean_io_error_to_string(v_a_4359_);
v___x_4362_ = lean_string_append(v___x_4360_, v___x_4361_);
lean_dec_ref(v___x_4361_);
v___x_4363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set_uint8(v___x_4363_, sizeof(void*)*1, v___x_4343_);
v___x_4364_ = lean_array_push(v___x_4345_, v___x_4363_);
v___x_4365_ = l_Lake_copyFile(v_path_4324_, v_file_4303_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_dec_ref_known(v___x_4365_, 1);
v___x_4366_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4366_, 0, v___x_4347_);
lean_ctor_set_uint8(v___x_4366_, 1, v___x_4322_);
lean_ctor_set_uint8(v___x_4366_, 2, v_exe_4305_);
lean_inc_ref_n(v___x_4366_, 2);
v___x_4367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
lean_ctor_set(v___x_4367_, 2, v___x_4366_);
v___x_4368_ = l_IO_setAccessRights(v_file_4303_, v___x_4367_);
lean_dec_ref_known(v___x_4367_, 3);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_dec_ref_known(v___x_4368_, 1);
v___y_4326_ = v___x_4364_;
goto v___jp_4325_;
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = lean_io_error_to_string(v_a_4369_);
v___x_4371_ = 3;
v___x_4372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set_uint8(v___x_4372_, sizeof(void*)*1, v___x_4371_);
v___x_4373_ = lean_array_get_size(v___x_4364_);
v___x_4374_ = lean_array_push(v___x_4364_, v___x_4372_);
v___x_4375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
return v___x_4375_;
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4376_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4377_ = lean_io_error_to_string(v_a_4376_);
v___x_4378_ = 3;
v___x_4379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set_uint8(v___x_4379_, sizeof(void*)*1, v___x_4378_);
v___x_4380_ = lean_array_get_size(v___x_4364_);
v___x_4381_ = lean_array_push(v___x_4364_, v___x_4379_);
v___x_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4380_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
return v___x_4382_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
lean_dec_ref(v_art_4304_);
lean_dec_ref(v_file_4303_);
v_a_4383_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4346_, 1);
v___x_4384_ = lean_io_error_to_string(v_a_4383_);
v___x_4385_ = 3;
v___x_4386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4386_, 0, v___x_4384_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*1, v___x_4385_);
v___x_4387_ = lean_array_get_size(v___x_4345_);
v___x_4388_ = lean_array_push(v___x_4345_, v___x_4386_);
v___x_4389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
return v___x_4389_;
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
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4390_, lean_object* v_art_4391_, lean_object* v_exe_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
uint8_t v_exe_boxed_4395_; lean_object* v_res_4396_; 
v_exe_boxed_4395_ = lean_unbox(v_exe_4392_);
v_res_4396_ = l_Lake_restoreArtifact(v_file_4390_, v_art_4391_, v_exe_boxed_4395_, v_a_4393_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4397_, lean_object* v_a_x3f_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v___x_4401_; lean_object* v_log_4402_; uint8_t v_action_4403_; uint8_t v_wantsRebuild_4404_; lean_object* v_trace_4405_; lean_object* v_buildTime_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4417_; 
v___x_4401_ = lean_io_mono_ms_now();
v_log_4402_ = lean_ctor_get(v___y_4399_, 0);
v_action_4403_ = lean_ctor_get_uint8(v___y_4399_, sizeof(void*)*3);
v_wantsRebuild_4404_ = lean_ctor_get_uint8(v___y_4399_, sizeof(void*)*3 + 1);
v_trace_4405_ = lean_ctor_get(v___y_4399_, 1);
v_buildTime_4406_ = lean_ctor_get(v___y_4399_, 2);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___y_4399_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4408_ = v___y_4399_;
v_isShared_4409_ = v_isSharedCheck_4417_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_buildTime_4406_);
lean_inc(v_trace_4405_);
lean_inc(v_log_4402_);
lean_dec(v___y_4399_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4417_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4410_ = lean_nat_sub(v___x_4401_, v_val_4397_);
lean_dec(v___x_4401_);
v___x_4411_ = lean_box(0);
v___x_4412_ = lean_nat_add(v_buildTime_4406_, v___x_4410_);
lean_dec(v___x_4410_);
lean_dec(v_buildTime_4406_);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 2, v___x_4412_);
v___x_4414_ = v___x_4408_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_log_4402_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_trace_4405_);
lean_ctor_set(v_reuseFailAlloc_4416_, 2, v___x_4412_);
lean_ctor_set_uint8(v_reuseFailAlloc_4416_, sizeof(void*)*3, v_action_4403_);
lean_ctor_set_uint8(v_reuseFailAlloc_4416_, sizeof(void*)*3 + 1, v_wantsRebuild_4404_);
v___x_4414_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4411_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
return v___x_4415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4418_, lean_object* v_a_x3f_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4418_, v_a_x3f_4419_, v___y_4420_);
lean_dec(v_a_x3f_4419_);
lean_dec(v_val_4418_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4423_, lean_object* v_build_4424_, lean_object* v_traceFile_4425_, lean_object* v_ext_4426_, uint8_t v_text_4427_, lean_object* v_a_4428_, lean_object* v_depTrace_4429_, lean_object* v_traceFile_4430_, uint8_t v_action_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v_a_4439_; lean_object* v_a_4440_; lean_object* v_log_4443_; uint8_t v_action_4444_; uint8_t v_wantsRebuild_4445_; lean_object* v_trace_4446_; lean_object* v_buildTime_4447_; lean_object* v_toBuildConfig_4453_; lean_object* v_log_4454_; uint8_t v_action_4455_; uint8_t v_wantsRebuild_4456_; lean_object* v_trace_4457_; lean_object* v_buildTime_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4637_; 
v_toBuildConfig_4453_ = lean_ctor_get(v_a_4435_, 0);
v_log_4454_ = lean_ctor_get(v_a_4436_, 0);
v_action_4455_ = lean_ctor_get_uint8(v_a_4436_, sizeof(void*)*3);
v_wantsRebuild_4456_ = lean_ctor_get_uint8(v_a_4436_, sizeof(void*)*3 + 1);
v_trace_4457_ = lean_ctor_get(v_a_4436_, 1);
v_buildTime_4458_ = lean_ctor_get(v_a_4436_, 2);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_a_4436_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4460_ = v_a_4436_;
v_isShared_4461_ = v_isSharedCheck_4637_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_buildTime_4458_);
lean_inc(v_trace_4457_);
lean_inc(v_log_4454_);
lean_dec(v_a_4436_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4637_;
goto v_resetjp_4459_;
}
v___jp_4438_:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4441_, 0, v_a_4439_);
lean_ctor_set(v___x_4441_, 1, v_a_4440_);
return v___x_4441_;
}
v___jp_4442_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4448_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4449_ = lean_array_get_size(v_log_4443_);
v___x_4450_ = lean_array_push(v_log_4443_, v___x_4448_);
v___x_4451_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
lean_ctor_set(v___x_4451_, 1, v_trace_4446_);
lean_ctor_set(v___x_4451_, 2, v_buildTime_4447_);
lean_ctor_set_uint8(v___x_4451_, sizeof(void*)*3, v_action_4444_);
lean_ctor_set_uint8(v___x_4451_, sizeof(void*)*3 + 1, v_wantsRebuild_4445_);
v___x_4452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4449_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
return v___x_4452_;
}
v_resetjp_4459_:
{
uint8_t v_noBuild_4462_; uint8_t v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_noBuild_4462_ = lean_ctor_get_uint8(v_toBuildConfig_4453_, sizeof(void*)*3 + 2);
v___x_4463_ = l_Lake_JobAction_merge(v_action_4455_, v_action_4431_);
v___x_4464_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4430_);
v___x_4465_ = l_System_FilePath_addExtension(v_traceFile_4430_, v___x_4464_);
if (v_noBuild_4462_ == 0)
{
lean_object* v___x_4466_; lean_object* v_a_4468_; lean_object* v_a_4469_; lean_object* v___x_4473_; 
v___x_4466_ = lean_io_mono_ms_now();
v___x_4473_ = l_Lake_removeFileIfExists(v_file_4423_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v___x_4475_; 
lean_dec_ref_known(v___x_4473_, 1);
lean_inc_ref(v_log_4454_);
if (v_isShared_4461_ == 0)
{
v___x_4475_ = v___x_4460_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_log_4454_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_trace_4457_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_buildTime_4458_);
lean_ctor_set_uint8(v_reuseFailAlloc_4612_, sizeof(void*)*3 + 1, v_wantsRebuild_4456_);
v___x_4475_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; 
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*3, v___x_4463_);
lean_inc_ref(v_a_4435_);
lean_inc(v_a_4434_);
lean_inc(v_a_4433_);
lean_inc(v_a_4432_);
v___x_4476_ = lean_apply_7(v_build_4424_, v_a_4428_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v___x_4475_, lean_box(0));
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v_log_4478_; uint8_t v_action_4479_; uint8_t v_wantsRebuild_4480_; lean_object* v_trace_4481_; lean_object* v_buildTime_4482_; lean_object* v___x_4483_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 2);
v_log_4478_ = lean_ctor_get(v_a_4477_, 0);
v_action_4479_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*3);
v_wantsRebuild_4480_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*3 + 1);
v_trace_4481_ = lean_ctor_get(v_a_4477_, 1);
v_buildTime_4482_ = lean_ctor_get(v_a_4477_, 2);
lean_inc_ref(v_file_4423_);
v___x_4483_ = l_Lake_clearFileHash(v_file_4423_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v___x_4484_; 
lean_dec_ref_known(v___x_4483_, 1);
v___x_4484_ = l_Lake_removeFileIfExists(v_traceFile_4425_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4576_; 
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4576_ == 0)
{
lean_object* v_unused_4577_; 
v_unused_4577_ = lean_ctor_get(v___x_4484_, 0);
lean_dec(v_unused_4577_);
v___x_4486_ = v___x_4484_;
v_isShared_4487_ = v_isSharedCheck_4576_;
goto v_resetjp_4485_;
}
else
{
lean_dec(v___x_4484_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4576_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lake_computeArtifact___redArg(v_file_4423_, v_ext_4426_, v_text_4427_, v_a_4435_, v_a_4477_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v_a_4490_; lean_object* v_descr_4491_; lean_object* v_log_4492_; uint8_t v_action_4493_; uint8_t v_wantsRebuild_4494_; lean_object* v_trace_4495_; lean_object* v_buildTime_4496_; uint64_t v_hash_4497_; lean_object* v_ext_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___y_4503_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_a_4489_);
v_a_4490_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4488_, 2);
v_descr_4491_ = lean_ctor_get(v_a_4490_, 0);
v_log_4492_ = lean_ctor_get(v_a_4489_, 0);
v_action_4493_ = lean_ctor_get_uint8(v_a_4489_, sizeof(void*)*3);
v_wantsRebuild_4494_ = lean_ctor_get_uint8(v_a_4489_, sizeof(void*)*3 + 1);
v_trace_4495_ = lean_ctor_get(v_a_4489_, 1);
v_buildTime_4496_ = lean_ctor_get(v_a_4489_, 2);
v_hash_4497_ = lean_ctor_get_uint64(v_descr_4491_, sizeof(void*)*1);
v_ext_4498_ = lean_ctor_get(v_descr_4491_, 0);
v___x_4499_ = lean_array_get_size(v_log_4454_);
lean_dec_ref(v_log_4454_);
v___x_4500_ = lean_array_get_size(v_log_4492_);
v___x_4501_ = l_Array_extract___redArg(v_log_4492_, v___x_4499_, v___x_4500_);
v___x_4566_ = lean_string_utf8_byte_size(v_ext_4498_);
v___x_4567_ = lean_unsigned_to_nat(0u);
v___x_4568_ = lean_nat_dec_eq(v___x_4566_, v___x_4567_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = l_Lake_lowerHexUInt64(v_hash_4497_);
v___x_4570_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4571_ = lean_string_append(v___x_4569_, v___x_4570_);
v___x_4572_ = lean_string_append(v___x_4571_, v_ext_4498_);
v___y_4503_ = v___x_4572_;
goto v___jp_4502_;
}
else
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lake_lowerHexUInt64(v_hash_4497_);
v___y_4503_ = v___x_4573_;
goto v___jp_4502_;
}
v___jp_4502_:
{
lean_object* v___x_4505_; 
if (v_isShared_4487_ == 0)
{
lean_ctor_set_tag(v___x_4486_, 3);
lean_ctor_set(v___x_4486_, 0, v___y_4503_);
v___x_4505_ = v___x_4486_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___y_4503_);
v___x_4505_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4429_, v___x_4505_, v___x_4501_);
v___x_4507_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4430_, v___x_4506_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4548_; 
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4548_ == 0)
{
lean_object* v_unused_4549_; 
v_unused_4549_ = lean_ctor_get(v___x_4507_, 0);
lean_dec(v_unused_4549_);
v___x_4509_ = v___x_4507_;
v_isShared_4510_ = v_isSharedCheck_4548_;
goto v_resetjp_4508_;
}
else
{
lean_dec(v___x_4507_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4548_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lake_removeFileIfExists(v___x_4465_);
lean_dec_ref(v___x_4465_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4531_; 
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4531_ == 0)
{
lean_object* v_unused_4532_; 
v_unused_4532_ = lean_ctor_get(v___x_4511_, 0);
lean_dec(v_unused_4532_);
v___x_4513_ = v___x_4511_;
v_isShared_4514_ = v_isSharedCheck_4531_;
goto v_resetjp_4512_;
}
else
{
lean_dec(v___x_4511_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4531_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
lean_inc(v_a_4490_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v_a_4490_);
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4490_);
v___x_4516_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4518_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set_tag(v___x_4509_, 1);
lean_ctor_set(v___x_4509_, 0, v___x_4516_);
v___x_4518_ = v___x_4509_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4516_);
v___x_4518_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
lean_object* v___x_4519_; lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
v___x_4519_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4466_, v___x_4518_, v_a_4489_);
lean_dec_ref(v___x_4518_);
lean_dec(v___x_4466_);
v_a_4520_ = lean_ctor_get(v___x_4519_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v___x_4519_, 0);
lean_dec(v_unused_4528_);
v___x_4522_ = v___x_4519_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v_a_4490_);
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4490_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
}
else
{
lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4544_; 
lean_inc(v_buildTime_4496_);
lean_inc_ref(v_trace_4495_);
lean_inc_ref(v_log_4492_);
lean_del_object(v___x_4509_);
lean_dec(v_a_4490_);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_a_4489_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; lean_object* v_unused_4546_; lean_object* v_unused_4547_; 
v_unused_4545_ = lean_ctor_get(v_a_4489_, 2);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_a_4489_, 1);
lean_dec(v_unused_4546_);
v_unused_4547_ = lean_ctor_get(v_a_4489_, 0);
lean_dec(v_unused_4547_);
v___x_4534_ = v_a_4489_;
v_isShared_4535_ = v_isSharedCheck_4544_;
goto v_resetjp_4533_;
}
else
{
lean_dec(v_a_4489_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4544_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v_a_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4542_; 
v_a_4536_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4511_, 1);
v___x_4537_ = lean_io_error_to_string(v_a_4536_);
v___x_4538_ = 3;
v___x_4539_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set_uint8(v___x_4539_, sizeof(void*)*1, v___x_4538_);
v___x_4540_ = lean_array_push(v_log_4492_, v___x_4539_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4540_);
v___x_4542_ = v___x_4534_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_trace_4495_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_buildTime_4496_);
lean_ctor_set_uint8(v_reuseFailAlloc_4543_, sizeof(void*)*3, v_action_4493_);
lean_ctor_set_uint8(v_reuseFailAlloc_4543_, sizeof(void*)*3 + 1, v_wantsRebuild_4494_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
v_a_4468_ = v___x_4500_;
v_a_4469_ = v___x_4542_;
goto v___jp_4467_;
}
}
}
}
}
else
{
lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4561_; 
lean_inc(v_buildTime_4496_);
lean_inc_ref(v_trace_4495_);
lean_inc_ref(v_log_4492_);
lean_dec(v_a_4490_);
lean_dec_ref(v___x_4465_);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_a_4489_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; lean_object* v_unused_4563_; lean_object* v_unused_4564_; 
v_unused_4562_ = lean_ctor_get(v_a_4489_, 2);
lean_dec(v_unused_4562_);
v_unused_4563_ = lean_ctor_get(v_a_4489_, 1);
lean_dec(v_unused_4563_);
v_unused_4564_ = lean_ctor_get(v_a_4489_, 0);
lean_dec(v_unused_4564_);
v___x_4551_ = v_a_4489_;
v_isShared_4552_ = v_isSharedCheck_4561_;
goto v_resetjp_4550_;
}
else
{
lean_dec(v_a_4489_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4561_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v_a_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
v_a_4553_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4507_, 1);
v___x_4554_ = lean_io_error_to_string(v_a_4553_);
v___x_4555_ = 3;
v___x_4556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*1, v___x_4555_);
v___x_4557_ = lean_array_push(v_log_4492_, v___x_4556_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4557_);
v___x_4559_ = v___x_4551_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_trace_4495_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_buildTime_4496_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*3, v_action_4493_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*3 + 1, v_wantsRebuild_4494_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
v_a_4468_ = v___x_4500_;
v_a_4469_ = v___x_4559_;
goto v___jp_4467_;
}
}
}
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v_a_4575_; 
lean_del_object(v___x_4486_);
lean_dec_ref(v___x_4465_);
lean_dec_ref(v_log_4454_);
lean_dec_ref(v_traceFile_4430_);
v_a_4574_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4574_);
v_a_4575_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4488_, 2);
v_a_4468_ = v_a_4574_;
v_a_4469_ = v_a_4575_;
goto v___jp_4467_;
}
}
}
else
{
lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4590_; 
lean_inc(v_buildTime_4482_);
lean_inc_ref(v_trace_4481_);
lean_inc_ref(v_log_4478_);
lean_dec_ref(v___x_4465_);
lean_dec_ref(v_log_4454_);
lean_dec_ref(v_traceFile_4430_);
lean_dec_ref(v_ext_4426_);
lean_dec_ref(v_file_4423_);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; lean_object* v_unused_4592_; lean_object* v_unused_4593_; 
v_unused_4591_ = lean_ctor_get(v_a_4477_, 2);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_a_4477_, 1);
lean_dec(v_unused_4592_);
v_unused_4593_ = lean_ctor_get(v_a_4477_, 0);
lean_dec(v_unused_4593_);
v___x_4579_ = v_a_4477_;
v_isShared_4580_ = v_isSharedCheck_4590_;
goto v_resetjp_4578_;
}
else
{
lean_dec(v_a_4477_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4590_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v_a_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v_a_4581_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4484_, 1);
v___x_4582_ = lean_io_error_to_string(v_a_4581_);
v___x_4583_ = 3;
v___x_4584_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set_uint8(v___x_4584_, sizeof(void*)*1, v___x_4583_);
v___x_4585_ = lean_array_get_size(v_log_4478_);
v___x_4586_ = lean_array_push(v_log_4478_, v___x_4584_);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 0, v___x_4586_);
v___x_4588_ = v___x_4579_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4586_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_trace_4481_);
lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_buildTime_4482_);
lean_ctor_set_uint8(v_reuseFailAlloc_4589_, sizeof(void*)*3, v_action_4479_);
lean_ctor_set_uint8(v_reuseFailAlloc_4589_, sizeof(void*)*3 + 1, v_wantsRebuild_4480_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
v_a_4468_ = v___x_4585_;
v_a_4469_ = v___x_4588_;
goto v___jp_4467_;
}
}
}
}
else
{
lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4606_; 
lean_inc(v_buildTime_4482_);
lean_inc_ref(v_trace_4481_);
lean_inc_ref(v_log_4478_);
lean_dec_ref(v___x_4465_);
lean_dec_ref(v_log_4454_);
lean_dec_ref(v_traceFile_4430_);
lean_dec_ref(v_ext_4426_);
lean_dec_ref(v_file_4423_);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; lean_object* v_unused_4608_; lean_object* v_unused_4609_; 
v_unused_4607_ = lean_ctor_get(v_a_4477_, 2);
lean_dec(v_unused_4607_);
v_unused_4608_ = lean_ctor_get(v_a_4477_, 1);
lean_dec(v_unused_4608_);
v_unused_4609_ = lean_ctor_get(v_a_4477_, 0);
lean_dec(v_unused_4609_);
v___x_4595_ = v_a_4477_;
v_isShared_4596_ = v_isSharedCheck_4606_;
goto v_resetjp_4594_;
}
else
{
lean_dec(v_a_4477_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4606_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v_a_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4598_ = lean_io_error_to_string(v_a_4597_);
v___x_4599_ = 3;
v___x_4600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4600_, 0, v___x_4598_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*1, v___x_4599_);
v___x_4601_ = lean_array_get_size(v_log_4478_);
v___x_4602_ = lean_array_push(v_log_4478_, v___x_4600_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4602_);
v___x_4604_ = v___x_4595_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_trace_4481_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_buildTime_4482_);
lean_ctor_set_uint8(v_reuseFailAlloc_4605_, sizeof(void*)*3, v_action_4479_);
lean_ctor_set_uint8(v_reuseFailAlloc_4605_, sizeof(void*)*3 + 1, v_wantsRebuild_4480_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
v_a_4468_ = v___x_4601_;
v_a_4469_ = v___x_4604_;
goto v___jp_4467_;
}
}
}
}
else
{
lean_object* v_a_4610_; lean_object* v_a_4611_; 
lean_dec_ref(v___x_4465_);
lean_dec_ref(v_log_4454_);
lean_dec_ref(v_traceFile_4430_);
lean_dec_ref(v_ext_4426_);
lean_dec_ref(v_file_4423_);
v_a_4610_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4610_);
v_a_4611_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_a_4611_);
lean_dec_ref_known(v___x_4476_, 2);
v_a_4468_ = v_a_4610_;
v_a_4469_ = v_a_4611_;
goto v___jp_4467_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_dec_ref(v___x_4465_);
lean_dec_ref(v_traceFile_4430_);
lean_dec_ref(v_a_4428_);
lean_dec_ref(v_ext_4426_);
lean_dec_ref(v_build_4424_);
lean_dec_ref(v_file_4423_);
v_a_4613_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4614_ = lean_io_error_to_string(v_a_4613_);
v___x_4615_ = 3;
v___x_4616_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4616_, 0, v___x_4614_);
lean_ctor_set_uint8(v___x_4616_, sizeof(void*)*1, v___x_4615_);
v___x_4617_ = lean_array_get_size(v_log_4454_);
v___x_4618_ = lean_array_push(v_log_4454_, v___x_4616_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4618_);
v___x_4620_ = v___x_4460_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_trace_4457_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_buildTime_4458_);
lean_ctor_set_uint8(v_reuseFailAlloc_4621_, sizeof(void*)*3 + 1, v_wantsRebuild_4456_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*3, v___x_4463_);
v_a_4468_ = v___x_4617_;
v_a_4469_ = v___x_4620_;
goto v___jp_4467_;
}
}
v___jp_4467_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v_a_4472_; 
v___x_4470_ = lean_box(0);
v___x_4471_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4466_, v___x_4470_, v_a_4469_);
lean_dec(v___x_4466_);
v_a_4472_ = lean_ctor_get(v___x_4471_, 1);
lean_inc(v_a_4472_);
lean_dec_ref(v___x_4471_);
v_a_4439_ = v_a_4468_;
v_a_4440_ = v_a_4472_;
goto v___jp_4438_;
}
}
else
{
uint8_t v___x_4622_; 
lean_dec_ref(v_a_4428_);
lean_dec_ref(v_ext_4426_);
lean_dec_ref(v_build_4424_);
lean_dec_ref(v_file_4423_);
v___x_4622_ = l_System_FilePath_pathExists(v_traceFile_4430_);
lean_dec_ref(v_traceFile_4430_);
if (v___x_4622_ == 0)
{
lean_dec_ref(v___x_4465_);
lean_del_object(v___x_4460_);
v_log_4443_ = v_log_4454_;
v_action_4444_ = v___x_4463_;
v_wantsRebuild_4445_ = v_noBuild_4462_;
v_trace_4446_ = v_trace_4457_;
v_buildTime_4447_ = v_buildTime_4458_;
goto v___jp_4442_;
}
else
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4623_ = lean_box(0);
v___x_4624_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4625_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4429_, v___x_4623_, v___x_4624_);
v___x_4626_ = l_Lake_BuildMetadata_writeFile(v___x_4465_, v___x_4625_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_dec_ref_known(v___x_4626_, 1);
lean_del_object(v___x_4460_);
v_log_4443_ = v_log_4454_;
v_action_4444_ = v___x_4463_;
v_wantsRebuild_4445_ = v_noBuild_4462_;
v_trace_4446_ = v_trace_4457_;
v_buildTime_4447_ = v_buildTime_4458_;
goto v___jp_4442_;
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v___x_4628_ = lean_io_error_to_string(v_a_4627_);
v___x_4629_ = 3;
v___x_4630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*1, v___x_4629_);
v___x_4631_ = lean_array_get_size(v_log_4454_);
v___x_4632_ = lean_array_push(v_log_4454_, v___x_4630_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4632_);
v___x_4634_ = v___x_4460_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_trace_4457_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_buildTime_4458_);
v___x_4634_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4635_; 
lean_ctor_set_uint8(v___x_4634_, sizeof(void*)*3, v___x_4463_);
lean_ctor_set_uint8(v___x_4634_, sizeof(void*)*3 + 1, v_noBuild_4462_);
v___x_4635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4631_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
return v___x_4635_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4638_, lean_object* v_build_4639_, lean_object* v_traceFile_4640_, lean_object* v_ext_4641_, lean_object* v_text_4642_, lean_object* v_a_4643_, lean_object* v_depTrace_4644_, lean_object* v_traceFile_4645_, lean_object* v_action_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
uint8_t v_text_boxed_4653_; uint8_t v_action_boxed_4654_; lean_object* v_res_4655_; 
v_text_boxed_4653_ = lean_unbox(v_text_4642_);
v_action_boxed_4654_ = lean_unbox(v_action_4646_);
v_res_4655_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4638_, v_build_4639_, v_traceFile_4640_, v_ext_4641_, v_text_boxed_4653_, v_a_4643_, v_depTrace_4644_, v_traceFile_4645_, v_action_boxed_4654_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_depTrace_4644_);
lean_dec_ref(v_traceFile_4640_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4656_, lean_object* v_build_4657_, uint8_t v_text_4658_, lean_object* v_ext_4659_, lean_object* v_depTrace_4660_, lean_object* v_traceFile_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
uint8_t v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = 5;
lean_inc_ref(v_traceFile_4661_);
v___x_4670_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4656_, v_build_4657_, v_traceFile_4661_, v_ext_4659_, v_text_4658_, v_a_4662_, v_depTrace_4660_, v_traceFile_4661_, v___x_4669_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec_ref(v_traceFile_4661_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4671_, lean_object* v_build_4672_, lean_object* v_text_4673_, lean_object* v_ext_4674_, lean_object* v_depTrace_4675_, lean_object* v_traceFile_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
uint8_t v_text_boxed_4684_; lean_object* v_res_4685_; 
v_text_boxed_4684_ = lean_unbox(v_text_4673_);
v_res_4685_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4671_, v_build_4672_, v_text_boxed_4684_, v_ext_4674_, v_depTrace_4675_, v_traceFile_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_depTrace_4675_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4687_, lean_object* v_traceFile_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_log_4691_; uint8_t v_action_4692_; uint8_t v_wantsRebuild_4693_; lean_object* v_trace_4694_; lean_object* v_buildTime_4695_; lean_object* v___x_4696_; 
v_log_4691_ = lean_ctor_get(v_a_4689_, 0);
v_action_4692_ = lean_ctor_get_uint8(v_a_4689_, sizeof(void*)*3);
v_wantsRebuild_4693_ = lean_ctor_get_uint8(v_a_4689_, sizeof(void*)*3 + 1);
v_trace_4694_ = lean_ctor_get(v_a_4689_, 1);
v_buildTime_4695_ = lean_ctor_get(v_a_4689_, 2);
v___x_4696_ = lean_io_metadata(v_traceFile_4688_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v_modified_4698_; lean_object* v_descr_4699_; lean_object* v_path_4700_; lean_object* v_name_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4709_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___x_4696_, 1);
v_modified_4698_ = lean_ctor_get(v_a_4697_, 1);
lean_inc_ref(v_modified_4698_);
lean_dec(v_a_4697_);
v_descr_4699_ = lean_ctor_get(v_art_4687_, 0);
v_path_4700_ = lean_ctor_get(v_art_4687_, 1);
v_name_4701_ = lean_ctor_get(v_art_4687_, 2);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_art_4687_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v_art_4687_, 3);
lean_dec(v_unused_4710_);
v___x_4703_ = v_art_4687_;
v_isShared_4704_ = v_isSharedCheck_4709_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_name_4701_);
lean_inc(v_path_4700_);
lean_inc(v_descr_4699_);
lean_dec(v_art_4687_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4709_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 3, v_modified_4698_);
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_descr_4699_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_path_4700_);
lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_name_4701_);
lean_ctor_set(v_reuseFailAlloc_4708_, 3, v_modified_4698_);
v___x_4706_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
lean_ctor_set(v___x_4707_, 1, v_a_4689_);
return v___x_4707_;
}
}
}
else
{
lean_object* v_a_4711_; 
v_a_4711_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4696_, 1);
if (lean_obj_tag(v_a_4711_) == 11)
{
lean_object* v___x_4712_; 
lean_dec_ref_known(v_a_4711_, 2);
v___x_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4712_, 0, v_art_4687_);
lean_ctor_set(v___x_4712_, 1, v_a_4689_);
return v___x_4712_;
}
else
{
lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4727_; 
lean_inc(v_buildTime_4695_);
lean_inc_ref(v_trace_4694_);
lean_inc_ref(v_log_4691_);
lean_dec_ref(v_art_4687_);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_a_4689_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; lean_object* v_unused_4729_; lean_object* v_unused_4730_; 
v_unused_4728_ = lean_ctor_get(v_a_4689_, 2);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_a_4689_, 1);
lean_dec(v_unused_4729_);
v_unused_4730_ = lean_ctor_get(v_a_4689_, 0);
lean_dec(v_unused_4730_);
v___x_4714_ = v_a_4689_;
v_isShared_4715_ = v_isSharedCheck_4727_;
goto v_resetjp_4713_;
}
else
{
lean_dec(v_a_4689_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4727_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4716_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4717_ = lean_io_error_to_string(v_a_4711_);
v___x_4718_ = lean_string_append(v___x_4716_, v___x_4717_);
lean_dec_ref(v___x_4717_);
v___x_4719_ = 3;
v___x_4720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set_uint8(v___x_4720_, sizeof(void*)*1, v___x_4719_);
v___x_4721_ = lean_array_get_size(v_log_4691_);
v___x_4722_ = lean_array_push(v_log_4691_, v___x_4720_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v___x_4722_);
v___x_4724_ = v___x_4714_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_trace_4694_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_buildTime_4695_);
lean_ctor_set_uint8(v_reuseFailAlloc_4726_, sizeof(void*)*3, v_action_4692_);
lean_ctor_set_uint8(v_reuseFailAlloc_4726_, sizeof(void*)*3 + 1, v_wantsRebuild_4693_);
v___x_4724_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; 
v___x_4725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4721_);
lean_ctor_set(v___x_4725_, 1, v___x_4724_);
return v___x_4725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4731_, lean_object* v_traceFile_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4731_, v_traceFile_4732_, v_a_4733_);
lean_dec_ref(v_traceFile_4732_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4736_, lean_object* v_traceFile_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4736_, v_traceFile_4737_, v_a_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4746_, lean_object* v_traceFile_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4746_, v_traceFile_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec_ref(v_traceFile_4747_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4756_, lean_object* v_____r_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4765_, 0, v_a_4756_);
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
v___x_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
lean_ctor_set(v___x_4767_, 1, v___y_4763_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4768_, lean_object* v_____r_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4768_, v_____r_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4778_, lean_object* v___y_4779_, uint64_t v_inputHash_4780_, lean_object* v_savedTrace_4781_, lean_object* v_pkg_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v___y_4790_; lean_object* v_a_4794_; lean_object* v_a_4795_; lean_object* v___y_4810_; 
if (lean_obj_tag(v_savedTrace_4781_) == 2)
{
lean_object* v_data_4825_; uint64_t v_depHash_4826_; lean_object* v_outputs_x3f_4827_; uint8_t v___x_4828_; 
v_data_4825_ = lean_ctor_get(v_savedTrace_4781_, 0);
lean_inc_ref(v_data_4825_);
lean_dec_ref_known(v_savedTrace_4781_, 1);
v_depHash_4826_ = lean_ctor_get_uint64(v_data_4825_, sizeof(void*)*3);
v_outputs_x3f_4827_ = lean_ctor_get(v_data_4825_, 1);
lean_inc(v_outputs_x3f_4827_);
lean_dec_ref(v_data_4825_);
v___x_4828_ = lean_uint64_dec_eq(v_depHash_4826_, v_inputHash_4780_);
if (v___x_4828_ == 0)
{
lean_dec(v_outputs_x3f_4827_);
lean_dec_ref(v_pkg_4782_);
lean_dec_ref(v___y_4779_);
v___y_4790_ = v_a_4787_;
goto v___jp_4789_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4827_) == 1)
{
lean_object* v_val_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v_val_4829_ = lean_ctor_get(v_outputs_x3f_4827_, 0);
lean_inc_n(v_val_4829_, 2);
lean_dec_ref_known(v_outputs_x3f_4827_, 1);
v___x_4830_ = lean_box(0);
v___x_4831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4831_, 0, v_val_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
lean_ctor_set(v___x_4831_, 2, v___x_4830_);
lean_inc_ref(v___y_4779_);
v___x_4832_ = l_Lake_resolveArtifactOutput(v___x_4831_, v_exe_4778_, v___y_4779_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_config_4833_; lean_object* v_a_4834_; lean_object* v_a_4835_; lean_object* v_enableArtifactCache_x3f_4836_; lean_object* v_a_4838_; uint8_t v_a_4842_; lean_object* v_a_4843_; 
v_config_4833_ = lean_ctor_get(v_pkg_4782_, 6);
v_a_4834_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4834_);
v_a_4835_ = lean_ctor_get(v___x_4832_, 1);
lean_inc(v_a_4835_);
lean_dec_ref_known(v___x_4832_, 2);
v_enableArtifactCache_x3f_4836_ = lean_ctor_get(v_config_4833_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4836_) == 0)
{
lean_object* v_toContext_4875_; lean_object* v_lakeEnv_4876_; lean_object* v_enableArtifactCache_x3f_4877_; 
v_toContext_4875_ = lean_ctor_get(v_a_4786_, 1);
v_lakeEnv_4876_ = lean_ctor_get(v_toContext_4875_, 0);
v_enableArtifactCache_x3f_4877_ = lean_ctor_get(v_lakeEnv_4876_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4877_) == 0)
{
lean_object* v_packages_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v_config_4881_; lean_object* v_enableArtifactCache_x3f_4882_; 
v_packages_4878_ = lean_ctor_get(v_toContext_4875_, 4);
v___x_4879_ = lean_unsigned_to_nat(0u);
v___x_4880_ = lean_array_fget_borrowed(v_packages_4878_, v___x_4879_);
v_config_4881_ = lean_ctor_get(v___x_4880_, 6);
v_enableArtifactCache_x3f_4882_ = lean_ctor_get(v_config_4881_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4882_) == 0)
{
lean_dec(v_val_4829_);
lean_dec_ref(v_pkg_4782_);
v_a_4838_ = v_a_4835_;
goto v___jp_4837_;
}
else
{
lean_object* v_val_4883_; uint8_t v___x_4884_; 
v_val_4883_ = lean_ctor_get(v_enableArtifactCache_x3f_4882_, 0);
v___x_4884_ = lean_unbox(v_val_4883_);
v_a_4842_ = v___x_4884_;
v_a_4843_ = v_a_4835_;
goto v___jp_4841_;
}
}
else
{
lean_object* v_val_4885_; uint8_t v___x_4886_; 
v_val_4885_ = lean_ctor_get(v_enableArtifactCache_x3f_4877_, 0);
v___x_4886_ = lean_unbox(v_val_4885_);
v_a_4842_ = v___x_4886_;
v_a_4843_ = v_a_4835_;
goto v___jp_4841_;
}
}
else
{
lean_object* v_val_4887_; uint8_t v___x_4888_; 
v_val_4887_ = lean_ctor_get(v_enableArtifactCache_x3f_4836_, 0);
v___x_4888_ = lean_unbox(v_val_4887_);
v_a_4842_ = v___x_4888_;
v_a_4843_ = v_a_4835_;
goto v___jp_4841_;
}
v___jp_4837_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = lean_box(0);
v___x_4840_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4834_, v___x_4839_, v___y_4779_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4838_);
lean_dec_ref(v___y_4779_);
v___y_4810_ = v___x_4840_;
goto v___jp_4809_;
}
v___jp_4841_:
{
if (v_a_4842_ == 0)
{
lean_dec(v_val_4829_);
lean_dec_ref(v_pkg_4782_);
v_a_4838_ = v_a_4843_;
goto v___jp_4837_;
}
else
{
lean_object* v_toContext_4844_; lean_object* v_log_4845_; uint8_t v_action_4846_; uint8_t v_wantsRebuild_4847_; lean_object* v_trace_4848_; lean_object* v_buildTime_4849_; lean_object* v_lakeCache_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; lean_object* v___x_4853_; 
v_toContext_4844_ = lean_ctor_get(v_a_4786_, 1);
v_log_4845_ = lean_ctor_get(v_a_4843_, 0);
v_action_4846_ = lean_ctor_get_uint8(v_a_4843_, sizeof(void*)*3);
v_wantsRebuild_4847_ = lean_ctor_get_uint8(v_a_4843_, sizeof(void*)*3 + 1);
v_trace_4848_ = lean_ctor_get(v_a_4843_, 1);
v_buildTime_4849_ = lean_ctor_get(v_a_4843_, 2);
v_lakeCache_4850_ = lean_ctor_get(v_toContext_4844_, 2);
v___x_4851_ = l_Lake_Package_cacheScope(v_pkg_4782_);
v___x_4852_ = 0;
lean_inc_ref(v_lakeCache_4850_);
v___x_4853_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4850_, v___x_4851_, v_inputHash_4780_, v_val_4829_, v___x_4830_, v___x_4830_, v___x_4852_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
lean_dec_ref_known(v___x_4853_, 1);
v___x_4854_ = lean_box(0);
v___x_4855_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4834_, v___x_4854_, v___y_4779_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4843_);
lean_dec_ref(v___y_4779_);
v___y_4810_ = v___x_4855_;
goto v___jp_4809_;
}
else
{
lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4871_; 
lean_inc(v_buildTime_4849_);
lean_inc_ref(v_trace_4848_);
lean_inc_ref(v_log_4845_);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_a_4843_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; 
v_unused_4872_ = lean_ctor_get(v_a_4843_, 2);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_a_4843_, 1);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_a_4843_, 0);
lean_dec(v_unused_4874_);
v___x_4857_ = v_a_4843_;
v_isShared_4858_ = v_isSharedCheck_4871_;
goto v_resetjp_4856_;
}
else
{
lean_dec(v_a_4843_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4871_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v_a_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4868_; 
v_a_4859_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4853_, 1);
v___x_4860_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4861_ = lean_io_error_to_string(v_a_4859_);
v___x_4862_ = lean_string_append(v___x_4860_, v___x_4861_);
lean_dec_ref(v___x_4861_);
v___x_4863_ = 2;
v___x_4864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set_uint8(v___x_4864_, sizeof(void*)*1, v___x_4863_);
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_array_push(v_log_4845_, v___x_4864_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4866_);
v___x_4868_ = v___x_4857_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_trace_4848_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v_buildTime_4849_);
lean_ctor_set_uint8(v_reuseFailAlloc_4870_, sizeof(void*)*3, v_action_4846_);
lean_ctor_set_uint8(v_reuseFailAlloc_4870_, sizeof(void*)*3 + 1, v_wantsRebuild_4847_);
v___x_4868_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4834_, v___x_4865_, v___y_4779_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v___x_4868_);
lean_dec_ref(v___y_4779_);
v___y_4810_ = v___x_4869_;
goto v___jp_4809_;
}
}
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v_a_4890_; 
lean_dec(v_val_4829_);
lean_dec_ref(v_pkg_4782_);
lean_dec_ref(v___y_4779_);
v_a_4889_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4889_);
v_a_4890_ = lean_ctor_get(v___x_4832_, 1);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4832_, 2);
v_a_4794_ = v_a_4889_;
v_a_4795_ = v_a_4890_;
goto v___jp_4793_;
}
}
else
{
lean_dec(v_outputs_x3f_4827_);
lean_dec_ref(v_pkg_4782_);
lean_dec_ref(v___y_4779_);
v___y_4790_ = v_a_4787_;
goto v___jp_4789_;
}
}
}
else
{
lean_dec_ref(v_pkg_4782_);
lean_dec(v_savedTrace_4781_);
lean_dec_ref(v___y_4779_);
v___y_4790_ = v_a_4787_;
goto v___jp_4789_;
}
v___jp_4789_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_box(0);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
lean_ctor_set(v___x_4792_, 1, v___y_4790_);
return v___x_4792_;
}
v___jp_4793_:
{
lean_object* v_log_4796_; uint8_t v_action_4797_; uint8_t v_wantsRebuild_4798_; lean_object* v_trace_4799_; lean_object* v_buildTime_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4808_; 
v_log_4796_ = lean_ctor_get(v_a_4795_, 0);
v_action_4797_ = lean_ctor_get_uint8(v_a_4795_, sizeof(void*)*3);
v_wantsRebuild_4798_ = lean_ctor_get_uint8(v_a_4795_, sizeof(void*)*3 + 1);
v_trace_4799_ = lean_ctor_get(v_a_4795_, 1);
v_buildTime_4800_ = lean_ctor_get(v_a_4795_, 2);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_a_4795_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4802_ = v_a_4795_;
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_buildTime_4800_);
lean_inc(v_trace_4799_);
lean_inc(v_log_4796_);
lean_dec(v_a_4795_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4804_; lean_object* v___x_4806_; 
v___x_4804_ = l_Array_shrink___redArg(v_log_4796_, v_a_4794_);
lean_dec(v_a_4794_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4804_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_trace_4799_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_buildTime_4800_);
lean_ctor_set_uint8(v_reuseFailAlloc_4807_, sizeof(void*)*3, v_action_4797_);
lean_ctor_set_uint8(v_reuseFailAlloc_4807_, sizeof(void*)*3 + 1, v_wantsRebuild_4798_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
v___y_4790_ = v___x_4806_;
goto v___jp_4789_;
}
}
}
v___jp_4809_:
{
if (lean_obj_tag(v___y_4810_) == 0)
{
lean_object* v_a_4811_; 
v_a_4811_ = lean_ctor_get(v___y_4810_, 0);
if (lean_obj_tag(v_a_4811_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4820_; 
lean_inc_ref(v_a_4811_);
v_a_4812_ = lean_ctor_get(v___y_4810_, 1);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___y_4810_);
if (v_isSharedCheck_4820_ == 0)
{
lean_object* v_unused_4821_; 
v_unused_4821_ = lean_ctor_get(v___y_4810_, 0);
lean_dec(v_unused_4821_);
v___x_4814_ = v___y_4810_;
v_isShared_4815_ = v_isSharedCheck_4820_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___y_4810_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4820_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v_a_4816_; lean_object* v___x_4818_; 
v_a_4816_ = lean_ctor_get(v_a_4811_, 0);
lean_inc(v_a_4816_);
lean_dec_ref_known(v_a_4811_, 1);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v_a_4816_);
v___x_4818_ = v___x_4814_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4816_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_a_4812_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
else
{
lean_object* v_a_4822_; 
v_a_4822_ = lean_ctor_get(v___y_4810_, 1);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___y_4810_, 2);
v___y_4790_ = v_a_4822_;
goto v___jp_4789_;
}
}
else
{
lean_object* v_a_4823_; lean_object* v_a_4824_; 
v_a_4823_ = lean_ctor_get(v___y_4810_, 0);
lean_inc(v_a_4823_);
v_a_4824_ = lean_ctor_get(v___y_4810_, 1);
lean_inc(v_a_4824_);
lean_dec_ref_known(v___y_4810_, 2);
v_a_4794_ = v_a_4823_;
v_a_4795_ = v_a_4824_;
goto v___jp_4793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4891_, lean_object* v___y_4892_, lean_object* v_inputHash_4893_, lean_object* v_savedTrace_4894_, lean_object* v_pkg_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_){
_start:
{
uint8_t v_exe_boxed_4902_; uint64_t v_inputHash_boxed_4903_; lean_object* v_res_4904_; 
v_exe_boxed_4902_ = lean_unbox(v_exe_4891_);
v_inputHash_boxed_4903_ = lean_unbox_uint64(v_inputHash_4893_);
lean_dec_ref(v_inputHash_4893_);
v_res_4904_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4902_, v___y_4892_, v_inputHash_boxed_4903_, v_savedTrace_4894_, v_pkg_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec(v_a_4896_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4905_, size_t v_i_4906_, size_t v_stop_4907_, lean_object* v_b_4908_){
_start:
{
uint8_t v___x_4909_; 
v___x_4909_ = lean_usize_dec_eq(v_i_4906_, v_stop_4907_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; lean_object* v_message_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; size_t v___x_4915_; size_t v___x_4916_; 
v___x_4910_ = lean_array_uget_borrowed(v_as_4905_, v_i_4906_);
v_message_4911_ = lean_ctor_get(v___x_4910_, 0);
v___x_4912_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4913_ = lean_string_append(v_b_4908_, v___x_4912_);
v___x_4914_ = lean_string_append(v___x_4913_, v_message_4911_);
v___x_4915_ = ((size_t)1ULL);
v___x_4916_ = lean_usize_add(v_i_4906_, v___x_4915_);
v_i_4906_ = v___x_4916_;
v_b_4908_ = v___x_4914_;
goto _start;
}
else
{
return v_b_4908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4918_, lean_object* v_i_4919_, lean_object* v_stop_4920_, lean_object* v_b_4921_){
_start:
{
size_t v_i_boxed_4922_; size_t v_stop_boxed_4923_; lean_object* v_res_4924_; 
v_i_boxed_4922_ = lean_unbox_usize(v_i_4919_);
lean_dec(v_i_4919_);
v_stop_boxed_4923_ = lean_unbox_usize(v_stop_4920_);
lean_dec(v_stop_4920_);
v_res_4924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4918_, v_i_boxed_4922_, v_stop_boxed_4923_, v_b_4921_);
lean_dec_ref(v_as_4918_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4925_, lean_object* v___y_4926_, uint64_t v_inputHash_4927_, lean_object* v_pkg_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_toContext_4935_; lean_object* v_log_4936_; uint8_t v_action_4937_; uint8_t v_wantsRebuild_4938_; lean_object* v_trace_4939_; lean_object* v_buildTime_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_5033_; 
v_toContext_4935_ = lean_ctor_get(v_a_4932_, 1);
v_log_4936_ = lean_ctor_get(v_a_4933_, 0);
v_action_4937_ = lean_ctor_get_uint8(v_a_4933_, sizeof(void*)*3);
v_wantsRebuild_4938_ = lean_ctor_get_uint8(v_a_4933_, sizeof(void*)*3 + 1);
v_trace_4939_ = lean_ctor_get(v_a_4933_, 1);
v_buildTime_4940_ = lean_ctor_get(v_a_4933_, 2);
v_isSharedCheck_5033_ = !lean_is_exclusive(v_a_4933_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_4942_ = v_a_4933_;
v_isShared_4943_ = v_isSharedCheck_5033_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_buildTime_4940_);
lean_inc(v_trace_4939_);
lean_inc(v_log_4936_);
lean_dec(v_a_4933_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_5033_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v_lakeCache_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v_lakeCache_4944_ = lean_ctor_get(v_toContext_4935_, 2);
v___x_4945_ = l_Lake_Package_cacheScope(v_pkg_4928_);
lean_inc_ref(v_lakeCache_4944_);
v___x_4946_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4944_, v___x_4945_, v_inputHash_4927_, v_log_4936_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5020_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_a_4948_ = lean_ctor_get(v___x_4946_, 1);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_4950_ = v___x_4946_;
v_isShared_4951_ = v_isSharedCheck_5020_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5020_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 0, v_a_4948_);
v___x_4953_ = v___x_4942_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_4948_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_trace_4939_);
lean_ctor_set(v_reuseFailAlloc_5019_, 2, v_buildTime_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_5019_, sizeof(void*)*3, v_action_4937_);
lean_ctor_set_uint8(v_reuseFailAlloc_5019_, sizeof(void*)*3 + 1, v_wantsRebuild_4938_);
v___x_4953_ = v_reuseFailAlloc_5019_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
if (lean_obj_tag(v_a_4947_) == 1)
{
lean_object* v_val_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5014_; 
v_val_4954_ = lean_ctor_get(v_a_4947_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_a_4947_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_4956_ = v_a_4947_;
v_isShared_4957_ = v_isSharedCheck_5014_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_val_4954_);
lean_dec(v_a_4947_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5014_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4958_; lean_object* v_r_4960_; lean_object* v___y_4961_; 
v___x_4958_ = l_Lake_resolveArtifactOutput(v_val_4954_, v_exe_4925_, v___y_4926_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v___x_4953_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4965_; lean_object* v_a_4966_; lean_object* v___x_4968_; 
v_a_4965_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4965_);
v_a_4966_ = lean_ctor_get(v___x_4958_, 1);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4958_, 2);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v_a_4965_);
v___x_4968_ = v___x_4956_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_a_4965_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
v_r_4960_ = v___x_4968_;
v___y_4961_ = v_a_4966_;
goto v___jp_4959_;
}
}
else
{
lean_object* v_a_4970_; lean_object* v_a_4971_; lean_object* v_log_4972_; uint8_t v_action_4973_; uint8_t v_wantsRebuild_4974_; lean_object* v_trace_4975_; lean_object* v_buildTime_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_5013_; 
lean_del_object(v___x_4956_);
v_a_4970_ = lean_ctor_get(v___x_4958_, 1);
lean_inc(v_a_4970_);
v_a_4971_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4958_, 2);
v_log_4972_ = lean_ctor_get(v_a_4970_, 0);
v_action_4973_ = lean_ctor_get_uint8(v_a_4970_, sizeof(void*)*3);
v_wantsRebuild_4974_ = lean_ctor_get_uint8(v_a_4970_, sizeof(void*)*3 + 1);
v_trace_4975_ = lean_ctor_get(v_a_4970_, 1);
v_buildTime_4976_ = lean_ctor_get(v_a_4970_, 2);
v_isSharedCheck_5013_ = !lean_is_exclusive(v_a_4970_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_4978_ = v_a_4970_;
v_isShared_4979_ = v_isSharedCheck_5013_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_buildTime_4976_);
lean_inc(v_trace_4975_);
lean_inc(v_log_4972_);
lean_dec(v_a_4970_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_5013_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___y_4984_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; uint8_t v___x_5005_; 
v___x_4980_ = lean_array_get_size(v_log_4972_);
lean_inc(v_a_4971_);
v___x_4981_ = l_Array_extract___redArg(v_log_4972_, v_a_4971_, v___x_4980_);
v___x_4982_ = l_Array_shrink___redArg(v_log_4972_, v_a_4971_);
lean_dec(v_a_4971_);
v___x_4992_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4993_ = l_Lake_lowerHexUInt64(v_inputHash_4927_);
v___x_4994_ = lean_unsigned_to_nat(7u);
v___x_4995_ = lean_unsigned_to_nat(0u);
v___x_4996_ = lean_string_utf8_byte_size(v___x_4993_);
lean_inc_ref(v___x_4993_);
v___x_4997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4993_);
lean_ctor_set(v___x_4997_, 1, v___x_4995_);
lean_ctor_set(v___x_4997_, 2, v___x_4996_);
v___x_4998_ = l_String_Slice_Pos_nextn(v___x_4997_, v___x_4995_, v___x_4994_);
lean_dec_ref_known(v___x_4997_, 3);
v___x_4999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4993_);
lean_ctor_set(v___x_4999_, 1, v___x_4995_);
lean_ctor_set(v___x_4999_, 2, v___x_4998_);
v___x_5000_ = l_String_Slice_toString(v___x_4999_);
lean_dec_ref_known(v___x_4999_, 3);
v___x_5001_ = lean_string_append(v___x_4992_, v___x_5000_);
lean_dec_ref(v___x_5000_);
v___x_5002_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_5003_ = lean_string_append(v___x_5001_, v___x_5002_);
v___x_5004_ = lean_array_get_size(v___x_4981_);
v___x_5005_ = lean_nat_dec_lt(v___x_4995_, v___x_5004_);
if (v___x_5005_ == 0)
{
lean_dec_ref(v___x_4981_);
v___y_4984_ = v___x_5003_;
goto v___jp_4983_;
}
else
{
uint8_t v___x_5006_; 
v___x_5006_ = lean_nat_dec_le(v___x_5004_, v___x_5004_);
if (v___x_5006_ == 0)
{
if (v___x_5005_ == 0)
{
lean_dec_ref(v___x_4981_);
v___y_4984_ = v___x_5003_;
goto v___jp_4983_;
}
else
{
size_t v___x_5007_; size_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5007_ = ((size_t)0ULL);
v___x_5008_ = lean_usize_of_nat(v___x_5004_);
v___x_5009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4981_, v___x_5007_, v___x_5008_, v___x_5003_);
lean_dec_ref(v___x_4981_);
v___y_4984_ = v___x_5009_;
goto v___jp_4983_;
}
}
else
{
size_t v___x_5010_; size_t v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((size_t)0ULL);
v___x_5011_ = lean_usize_of_nat(v___x_5004_);
v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4981_, v___x_5010_, v___x_5011_, v___x_5003_);
lean_dec_ref(v___x_4981_);
v___y_4984_ = v___x_5012_;
goto v___jp_4983_;
}
}
v___jp_4983_:
{
uint8_t v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4985_ = 2;
v___x_4986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4986_, 0, v___y_4984_);
lean_ctor_set_uint8(v___x_4986_, sizeof(void*)*1, v___x_4985_);
v___x_4987_ = lean_array_push(v___x_4982_, v___x_4986_);
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 0, v___x_4987_);
v___x_4989_ = v___x_4978_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_trace_4975_);
lean_ctor_set(v_reuseFailAlloc_4991_, 2, v_buildTime_4976_);
lean_ctor_set_uint8(v_reuseFailAlloc_4991_, sizeof(void*)*3, v_action_4973_);
lean_ctor_set_uint8(v_reuseFailAlloc_4991_, sizeof(void*)*3 + 1, v_wantsRebuild_4974_);
v___x_4989_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_box(0);
v_r_4960_ = v___x_4990_;
v___y_4961_ = v___x_4989_;
goto v___jp_4959_;
}
}
}
}
v___jp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 1, v___y_4961_);
lean_ctor_set(v___x_4950_, 0, v_r_4960_);
v___x_4963_ = v___x_4950_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_r_4960_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v___y_4961_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
lean_dec(v_a_4947_);
lean_dec_ref(v___y_4926_);
v___x_5015_ = lean_box(0);
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 1, v___x_4953_);
lean_ctor_set(v___x_4950_, 0, v___x_5015_);
v___x_5017_ = v___x_4950_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_4953_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5032_; 
lean_dec_ref(v___y_4926_);
v_a_5021_ = lean_ctor_get(v___x_4946_, 0);
v_a_5022_ = lean_ctor_get(v___x_4946_, 1);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5024_ = v___x_4946_;
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_inc(v_a_5021_);
lean_dec(v___x_4946_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 0, v_a_5022_);
v___x_5027_ = v___x_4942_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5022_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_trace_4939_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_buildTime_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_5031_, sizeof(void*)*3, v_action_4937_);
lean_ctor_set_uint8(v_reuseFailAlloc_5031_, sizeof(void*)*3 + 1, v_wantsRebuild_4938_);
v___x_5027_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5029_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v___x_5027_);
v___x_5029_ = v___x_5024_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5021_);
lean_ctor_set(v_reuseFailAlloc_5030_, 1, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_5034_, lean_object* v___y_5035_, lean_object* v_inputHash_5036_, lean_object* v_pkg_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
uint8_t v_exe_boxed_5044_; uint64_t v_inputHash_boxed_5045_; lean_object* v_res_5046_; 
v_exe_boxed_5044_ = lean_unbox(v_exe_5034_);
v_inputHash_boxed_5045_ = lean_unbox_uint64(v_inputHash_5036_);
lean_dec_ref(v_inputHash_5036_);
v_res_5046_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5044_, v___y_5035_, v_inputHash_boxed_5045_, v_pkg_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5047_, uint64_t v_hash_5048_, lean_object* v_a_5049_, lean_object* v_val_5050_, lean_object* v_file_5051_, lean_object* v___x_5052_, uint8_t v_restore_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_a_5062_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5106_; lean_object* v___y_5107_; uint8_t v___y_5108_; lean_object* v___y_5109_; uint8_t v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v_a_5127_; lean_object* v_val_5128_; lean_object* v_a_5129_; lean_object* v___y_5183_; lean_object* v_a_5189_; lean_object* v___y_5190_; lean_object* v___x_5192_; lean_object* v_a_5193_; 
lean_inc_ref(v_val_5050_);
lean_inc(v_a_5049_);
lean_inc_ref(v___y_5054_);
v___x_5192_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5047_, v___y_5054_, v_hash_5048_, v_a_5049_, v_val_5050_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_a_5193_);
if (lean_obj_tag(v_a_5193_) == 1)
{
lean_object* v_a_5194_; lean_object* v_val_5195_; 
lean_dec_ref(v___y_5054_);
lean_dec_ref(v_val_5050_);
v_a_5194_ = lean_ctor_get(v___x_5192_, 1);
lean_inc(v_a_5194_);
lean_dec_ref(v___x_5192_);
v_val_5195_ = lean_ctor_get(v_a_5193_, 0);
lean_inc(v_val_5195_);
lean_dec_ref_known(v_a_5193_, 1);
v_a_5189_ = v_val_5195_;
v___y_5190_ = v_a_5194_;
goto v___jp_5188_;
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5197_; 
lean_dec(v_a_5193_);
v_a_5196_ = lean_ctor_get(v___x_5192_, 1);
lean_inc(v_a_5196_);
lean_dec_ref(v___x_5192_);
v___x_5197_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5047_, v___y_5054_, v_hash_5048_, v_val_5050_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v_a_5196_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
if (lean_obj_tag(v_a_5198_) == 1)
{
lean_object* v_a_5199_; lean_object* v_val_5200_; 
v_a_5199_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_a_5199_);
lean_dec_ref_known(v___x_5197_, 2);
v_val_5200_ = lean_ctor_get(v_a_5198_, 0);
lean_inc(v_val_5200_);
lean_dec_ref_known(v_a_5198_, 1);
v_a_5189_ = v_val_5200_;
v___y_5190_ = v_a_5199_;
goto v___jp_5188_;
}
else
{
lean_object* v_a_5201_; 
lean_dec(v_a_5198_);
lean_dec_ref(v___x_5052_);
lean_dec_ref(v_file_5051_);
lean_dec(v_a_5049_);
v_a_5201_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5197_, 2);
v_a_5062_ = v_a_5201_;
goto v___jp_5061_;
}
}
else
{
v___y_5183_ = v___x_5197_;
goto v___jp_5182_;
}
}
v___jp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_box(0);
v___x_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
lean_ctor_set(v___x_5064_, 1, v_a_5062_);
return v___x_5064_;
}
v___jp_5065_:
{
if (v_restore_5053_ == 0)
{
lean_object* v___x_5069_; 
lean_dec_ref(v___y_5066_);
lean_dec_ref(v_file_5051_);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___y_5067_);
lean_ctor_set(v___x_5069_, 1, v___y_5068_);
return v___x_5069_;
}
else
{
lean_object* v_log_5070_; uint8_t v_action_5071_; uint8_t v_wantsRebuild_5072_; lean_object* v_trace_5073_; lean_object* v_buildTime_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5104_; 
lean_dec(v___y_5067_);
v_log_5070_ = lean_ctor_get(v___y_5068_, 0);
v_action_5071_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*3);
v_wantsRebuild_5072_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*3 + 1);
v_trace_5073_ = lean_ctor_get(v___y_5068_, 1);
v_buildTime_5074_ = lean_ctor_get(v___y_5068_, 2);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___y_5068_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5076_ = v___y_5068_;
v_isShared_5077_ = v_isSharedCheck_5104_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_buildTime_5074_);
lean_inc(v_trace_5073_);
lean_inc(v_log_5070_);
lean_dec(v___y_5068_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5104_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; 
v___x_5078_ = l_Lake_restoreArtifact(v_file_5051_, v___y_5066_, v_exe_5047_, v_log_5070_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5091_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
v_a_5080_ = lean_ctor_get(v___x_5078_, 1);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5082_ = v___x_5078_;
v_isShared_5083_ = v_isSharedCheck_5091_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_inc(v_a_5079_);
lean_dec(v___x_5078_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5091_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 0, v_a_5080_);
v___x_5085_ = v___x_5076_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5080_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v_trace_5073_);
lean_ctor_set(v_reuseFailAlloc_5090_, 2, v_buildTime_5074_);
lean_ctor_set_uint8(v_reuseFailAlloc_5090_, sizeof(void*)*3, v_action_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5090_, sizeof(void*)*3 + 1, v_wantsRebuild_5072_);
v___x_5085_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
v___x_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5086_, 0, v_a_5079_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 1, v___x_5085_);
lean_ctor_set(v___x_5082_, 0, v___x_5086_);
v___x_5088_ = v___x_5082_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___x_5085_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5103_; 
v_a_5092_ = lean_ctor_get(v___x_5078_, 0);
v_a_5093_ = lean_ctor_get(v___x_5078_, 1);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5095_ = v___x_5078_;
v_isShared_5096_ = v_isSharedCheck_5103_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_inc(v_a_5092_);
lean_dec(v___x_5078_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5103_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 0, v_a_5093_);
v___x_5098_ = v___x_5076_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5093_);
lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_trace_5073_);
lean_ctor_set(v_reuseFailAlloc_5102_, 2, v_buildTime_5074_);
lean_ctor_set_uint8(v_reuseFailAlloc_5102_, sizeof(void*)*3, v_action_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5102_, sizeof(void*)*3 + 1, v_wantsRebuild_5072_);
v___x_5098_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5100_; 
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 1, v___x_5098_);
v___x_5100_ = v___x_5095_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5092_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
}
}
v___jp_5105_:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___y_5113_);
v___x_5115_ = l_Lake_BuildMetadata_ofFetch(v_hash_5048_, v___x_5114_);
v___x_5116_ = l_Lake_BuildMetadata_writeFile(v___x_5052_, v___x_5115_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v___x_5117_; 
lean_dec_ref_known(v___x_5116_, 1);
v___x_5117_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5117_, 0, v___y_5109_);
lean_ctor_set(v___x_5117_, 1, v___y_5106_);
lean_ctor_set(v___x_5117_, 2, v___y_5111_);
lean_ctor_set_uint8(v___x_5117_, sizeof(void*)*3, v___y_5108_);
lean_ctor_set_uint8(v___x_5117_, sizeof(void*)*3 + 1, v___y_5110_);
v___y_5066_ = v___y_5107_;
v___y_5067_ = v___y_5112_;
v___y_5068_ = v___x_5117_;
goto v___jp_5065_;
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5107_);
lean_dec_ref(v_file_5051_);
v_a_5118_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5116_, 1);
v___x_5119_ = lean_io_error_to_string(v_a_5118_);
v___x_5120_ = 3;
v___x_5121_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5121_, 0, v___x_5119_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*1, v___x_5120_);
v___x_5122_ = lean_array_get_size(v___y_5109_);
v___x_5123_ = lean_array_push(v___y_5109_, v___x_5121_);
v___x_5124_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
lean_ctor_set(v___x_5124_, 1, v___y_5106_);
lean_ctor_set(v___x_5124_, 2, v___y_5111_);
lean_ctor_set_uint8(v___x_5124_, sizeof(void*)*3, v___y_5108_);
lean_ctor_set_uint8(v___x_5124_, sizeof(void*)*3 + 1, v___y_5110_);
v___x_5125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5125_, 0, v___x_5122_);
lean_ctor_set(v___x_5125_, 1, v___x_5124_);
return v___x_5125_;
}
}
v___jp_5126_:
{
lean_object* v___x_5130_; 
v___x_5130_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5048_, v_a_5049_, v_a_5129_);
lean_dec(v_a_5049_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; uint8_t v___x_5132_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
v___x_5132_ = lean_unbox(v_a_5131_);
lean_dec(v_a_5131_);
if (v___x_5132_ == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5170_; 
v_a_5133_ = lean_ctor_get(v___x_5130_, 1);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; 
v_unused_5171_ = lean_ctor_get(v___x_5130_, 0);
lean_dec(v_unused_5171_);
v___x_5135_ = v___x_5130_;
v_isShared_5136_ = v_isSharedCheck_5170_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5130_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5170_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v_log_5137_; uint8_t v_action_5138_; uint8_t v_wantsRebuild_5139_; lean_object* v_trace_5140_; lean_object* v_buildTime_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5169_; 
v_log_5137_ = lean_ctor_get(v_a_5133_, 0);
v_action_5138_ = lean_ctor_get_uint8(v_a_5133_, sizeof(void*)*3);
v_wantsRebuild_5139_ = lean_ctor_get_uint8(v_a_5133_, sizeof(void*)*3 + 1);
v_trace_5140_ = lean_ctor_get(v_a_5133_, 1);
v_buildTime_5141_ = lean_ctor_get(v_a_5133_, 2);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_a_5133_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5143_ = v_a_5133_;
v_isShared_5144_ = v_isSharedCheck_5169_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_buildTime_5141_);
lean_inc(v_trace_5140_);
lean_inc(v_log_5137_);
lean_dec(v_a_5133_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5169_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5145_; 
v___x_5145_ = l_Lake_removeFileIfExists(v_file_5051_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_descr_5146_; uint64_t v_hash_5147_; lean_object* v_ext_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; 
lean_dec_ref_known(v___x_5145_, 1);
lean_del_object(v___x_5143_);
lean_del_object(v___x_5135_);
v_descr_5146_ = lean_ctor_get(v_val_5128_, 0);
v_hash_5147_ = lean_ctor_get_uint64(v_descr_5146_, sizeof(void*)*1);
v_ext_5148_ = lean_ctor_get(v_descr_5146_, 0);
v___x_5149_ = lean_string_utf8_byte_size(v_ext_5148_);
v___x_5150_ = lean_unsigned_to_nat(0u);
v___x_5151_ = lean_nat_dec_eq(v___x_5149_, v___x_5150_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5152_ = l_Lake_lowerHexUInt64(v_hash_5147_);
v___x_5153_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5154_ = lean_string_append(v___x_5152_, v___x_5153_);
v___x_5155_ = lean_string_append(v___x_5154_, v_ext_5148_);
v___y_5106_ = v_trace_5140_;
v___y_5107_ = v_val_5128_;
v___y_5108_ = v_action_5138_;
v___y_5109_ = v_log_5137_;
v___y_5110_ = v_wantsRebuild_5139_;
v___y_5111_ = v_buildTime_5141_;
v___y_5112_ = v_a_5127_;
v___y_5113_ = v___x_5155_;
goto v___jp_5105_;
}
else
{
lean_object* v___x_5156_; 
v___x_5156_ = l_Lake_lowerHexUInt64(v_hash_5147_);
v___y_5106_ = v_trace_5140_;
v___y_5107_ = v_val_5128_;
v___y_5108_ = v_action_5138_;
v___y_5109_ = v_log_5137_;
v___y_5110_ = v_wantsRebuild_5139_;
v___y_5111_ = v_buildTime_5141_;
v___y_5112_ = v_a_5127_;
v___y_5113_ = v___x_5156_;
goto v___jp_5105_;
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5164_; 
lean_dec_ref(v_val_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v___x_5052_);
lean_dec_ref(v_file_5051_);
v_a_5157_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5157_);
lean_dec_ref_known(v___x_5145_, 1);
v___x_5158_ = lean_io_error_to_string(v_a_5157_);
v___x_5159_ = 3;
v___x_5160_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5160_, 0, v___x_5158_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1, v___x_5159_);
v___x_5161_ = lean_array_get_size(v_log_5137_);
v___x_5162_ = lean_array_push(v_log_5137_, v___x_5160_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5162_);
v___x_5164_ = v___x_5143_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5168_, 1, v_trace_5140_);
lean_ctor_set(v_reuseFailAlloc_5168_, 2, v_buildTime_5141_);
lean_ctor_set_uint8(v_reuseFailAlloc_5168_, sizeof(void*)*3, v_action_5138_);
lean_ctor_set_uint8(v_reuseFailAlloc_5168_, sizeof(void*)*3 + 1, v_wantsRebuild_5139_);
v___x_5164_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
lean_object* v___x_5166_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set_tag(v___x_5135_, 1);
lean_ctor_set(v___x_5135_, 1, v___x_5164_);
lean_ctor_set(v___x_5135_, 0, v___x_5161_);
v___x_5166_ = v___x_5135_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
}
else
{
lean_object* v_a_5172_; 
lean_dec_ref(v___x_5052_);
v_a_5172_ = lean_ctor_get(v___x_5130_, 1);
lean_inc(v_a_5172_);
lean_dec_ref_known(v___x_5130_, 2);
v___y_5066_ = v_val_5128_;
v___y_5067_ = v_a_5127_;
v___y_5068_ = v_a_5172_;
goto v___jp_5065_;
}
}
else
{
lean_object* v_a_5173_; lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_dec_ref(v_val_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v___x_5052_);
lean_dec_ref(v_file_5051_);
v_a_5173_ = lean_ctor_get(v___x_5130_, 0);
v_a_5174_ = lean_ctor_get(v___x_5130_, 1);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5130_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_inc(v_a_5173_);
lean_dec(v___x_5130_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5173_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_a_5174_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
}
v___jp_5182_:
{
if (lean_obj_tag(v___y_5183_) == 0)
{
lean_object* v_a_5184_; 
v_a_5184_ = lean_ctor_get(v___y_5183_, 0);
if (lean_obj_tag(v_a_5184_) == 1)
{
lean_object* v_a_5185_; lean_object* v_val_5186_; 
lean_inc_ref(v_a_5184_);
v_a_5185_ = lean_ctor_get(v___y_5183_, 1);
lean_inc(v_a_5185_);
lean_dec_ref_known(v___y_5183_, 2);
v_val_5186_ = lean_ctor_get(v_a_5184_, 0);
lean_inc(v_val_5186_);
v_a_5127_ = v_a_5184_;
v_val_5128_ = v_val_5186_;
v_a_5129_ = v_a_5185_;
goto v___jp_5126_;
}
else
{
lean_object* v_a_5187_; 
lean_dec_ref(v___x_5052_);
lean_dec_ref(v_file_5051_);
lean_dec(v_a_5049_);
v_a_5187_ = lean_ctor_get(v___y_5183_, 1);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___y_5183_, 2);
v_a_5062_ = v_a_5187_;
goto v___jp_5061_;
}
}
else
{
lean_dec_ref(v___x_5052_);
lean_dec_ref(v_file_5051_);
lean_dec(v_a_5049_);
return v___y_5183_;
}
}
v___jp_5188_:
{
lean_object* v___x_5191_; 
lean_inc_ref(v_a_5189_);
v___x_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5191_, 0, v_a_5189_);
v_a_5127_ = v___x_5191_;
v_val_5128_ = v_a_5189_;
v_a_5129_ = v___y_5190_;
goto v___jp_5126_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5202_, lean_object* v_hash_5203_, lean_object* v_a_5204_, lean_object* v_val_5205_, lean_object* v_file_5206_, lean_object* v___x_5207_, lean_object* v_restore_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
uint8_t v_exe_boxed_5216_; uint64_t v_hash_boxed_5217_; uint8_t v_restore_boxed_5218_; lean_object* v_res_5219_; 
v_exe_boxed_5216_ = lean_unbox(v_exe_5202_);
v_hash_boxed_5217_ = lean_unbox_uint64(v_hash_5203_);
lean_dec_ref(v_hash_5203_);
v_restore_boxed_5218_ = lean_unbox(v_restore_5208_);
v_res_5219_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5216_, v_hash_boxed_5217_, v_a_5204_, v_val_5205_, v_file_5206_, v___x_5207_, v_restore_boxed_5218_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec(v___y_5210_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5220_, lean_object* v_file_5221_, lean_object* v_ext_5222_, uint8_t v_text_5223_, uint8_t v_exe_5224_, uint8_t v___y_5225_, lean_object* v_val_5226_, uint64_t v_hash_5227_, uint8_t v_a_5228_, lean_object* v_____r_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
uint8_t v___x_5237_; uint8_t v___x_5238_; 
v___x_5237_ = 1;
v___x_5238_ = l_Lake_instDecidableEqOutputStatus(v_a_5220_, v___x_5237_);
if (v___x_5238_ == 0)
{
lean_object* v_toContext_5239_; lean_object* v_log_5240_; uint8_t v_action_5241_; uint8_t v_wantsRebuild_5242_; lean_object* v_trace_5243_; lean_object* v_buildTime_5244_; lean_object* v_lakeCache_5245_; lean_object* v___x_5246_; 
v_toContext_5239_ = lean_ctor_get(v___y_5234_, 1);
v_log_5240_ = lean_ctor_get(v___y_5235_, 0);
v_action_5241_ = lean_ctor_get_uint8(v___y_5235_, sizeof(void*)*3);
v_wantsRebuild_5242_ = lean_ctor_get_uint8(v___y_5235_, sizeof(void*)*3 + 1);
v_trace_5243_ = lean_ctor_get(v___y_5235_, 1);
v_buildTime_5244_ = lean_ctor_get(v___y_5235_, 2);
v_lakeCache_5245_ = lean_ctor_get(v_toContext_5239_, 2);
lean_inc_ref(v_lakeCache_5245_);
v___x_5246_ = l_Lake_Cache_saveArtifact(v_lakeCache_5245_, v_file_5221_, v_ext_5222_, v_text_5223_, v_exe_5224_, v___y_5225_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5288_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5288_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5288_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v_descr_5251_; uint64_t v_hash_5252_; lean_object* v_ext_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___y_5257_; lean_object* v___x_5280_; lean_object* v___x_5281_; uint8_t v___x_5282_; 
v_descr_5251_ = lean_ctor_get(v_a_5247_, 0);
v_hash_5252_ = lean_ctor_get_uint64(v_descr_5251_, sizeof(void*)*1);
v_ext_5253_ = lean_ctor_get(v_descr_5251_, 0);
v___x_5254_ = l_Lake_Package_cacheScope(v_val_5226_);
v___x_5255_ = lean_box(0);
v___x_5280_ = lean_string_utf8_byte_size(v_ext_5253_);
v___x_5281_ = lean_unsigned_to_nat(0u);
v___x_5282_ = lean_nat_dec_eq(v___x_5280_, v___x_5281_);
if (v___x_5282_ == 0)
{
lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5283_ = l_Lake_lowerHexUInt64(v_hash_5252_);
v___x_5284_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5285_ = lean_string_append(v___x_5283_, v___x_5284_);
v___x_5286_ = lean_string_append(v___x_5285_, v_ext_5253_);
v___y_5257_ = v___x_5286_;
goto v___jp_5256_;
}
else
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lake_lowerHexUInt64(v_hash_5252_);
v___y_5257_ = v___x_5287_;
goto v___jp_5256_;
}
v___jp_5256_:
{
lean_object* v___x_5259_; 
if (v_isShared_5250_ == 0)
{
lean_ctor_set_tag(v___x_5249_, 3);
lean_ctor_set(v___x_5249_, 0, v___y_5257_);
v___x_5259_ = v___x_5249_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___y_5257_);
v___x_5259_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
lean_object* v___x_5260_; 
lean_inc_ref(v_lakeCache_5245_);
v___x_5260_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5245_, v___x_5254_, v_hash_5227_, v___x_5259_, v___x_5255_, v___x_5255_, v_a_5228_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v___x_5261_; 
lean_dec_ref_known(v___x_5260_, 1);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v_a_5247_);
lean_ctor_set(v___x_5261_, 1, v___y_5235_);
return v___x_5261_;
}
else
{
lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5275_; 
lean_inc(v_buildTime_5244_);
lean_inc_ref(v_trace_5243_);
lean_inc_ref(v_log_5240_);
lean_dec(v_a_5247_);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___y_5235_);
if (v_isSharedCheck_5275_ == 0)
{
lean_object* v_unused_5276_; lean_object* v_unused_5277_; lean_object* v_unused_5278_; 
v_unused_5276_ = lean_ctor_get(v___y_5235_, 2);
lean_dec(v_unused_5276_);
v_unused_5277_ = lean_ctor_get(v___y_5235_, 1);
lean_dec(v_unused_5277_);
v_unused_5278_ = lean_ctor_get(v___y_5235_, 0);
lean_dec(v_unused_5278_);
v___x_5263_ = v___y_5235_;
v_isShared_5264_ = v_isSharedCheck_5275_;
goto v_resetjp_5262_;
}
else
{
lean_dec(v___y_5235_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5275_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v_a_5265_; lean_object* v___x_5266_; uint8_t v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5272_; 
v_a_5265_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_a_5265_);
lean_dec_ref_known(v___x_5260_, 1);
v___x_5266_ = lean_io_error_to_string(v_a_5265_);
v___x_5267_ = 3;
v___x_5268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5268_, 0, v___x_5266_);
lean_ctor_set_uint8(v___x_5268_, sizeof(void*)*1, v___x_5267_);
v___x_5269_ = lean_array_get_size(v_log_5240_);
v___x_5270_ = lean_array_push(v_log_5240_, v___x_5268_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 0, v___x_5270_);
v___x_5272_ = v___x_5263_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5270_);
lean_ctor_set(v_reuseFailAlloc_5274_, 1, v_trace_5243_);
lean_ctor_set(v_reuseFailAlloc_5274_, 2, v_buildTime_5244_);
lean_ctor_set_uint8(v_reuseFailAlloc_5274_, sizeof(void*)*3, v_action_5241_);
lean_ctor_set_uint8(v_reuseFailAlloc_5274_, sizeof(void*)*3 + 1, v_wantsRebuild_5242_);
v___x_5272_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; 
v___x_5273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5269_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
return v___x_5273_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5302_; 
lean_inc(v_buildTime_5244_);
lean_inc_ref(v_trace_5243_);
lean_inc_ref(v_log_5240_);
lean_dec_ref(v_val_5226_);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___y_5235_);
if (v_isSharedCheck_5302_ == 0)
{
lean_object* v_unused_5303_; lean_object* v_unused_5304_; lean_object* v_unused_5305_; 
v_unused_5303_ = lean_ctor_get(v___y_5235_, 2);
lean_dec(v_unused_5303_);
v_unused_5304_ = lean_ctor_get(v___y_5235_, 1);
lean_dec(v_unused_5304_);
v_unused_5305_ = lean_ctor_get(v___y_5235_, 0);
lean_dec(v_unused_5305_);
v___x_5290_ = v___y_5235_;
v_isShared_5291_ = v_isSharedCheck_5302_;
goto v_resetjp_5289_;
}
else
{
lean_dec(v___y_5235_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5302_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v_a_5292_; lean_object* v___x_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5299_; 
v_a_5292_ = lean_ctor_get(v___x_5246_, 0);
lean_inc(v_a_5292_);
lean_dec_ref_known(v___x_5246_, 1);
v___x_5293_ = lean_io_error_to_string(v_a_5292_);
v___x_5294_ = 3;
v___x_5295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5295_, 0, v___x_5293_);
lean_ctor_set_uint8(v___x_5295_, sizeof(void*)*1, v___x_5294_);
v___x_5296_ = lean_array_get_size(v_log_5240_);
v___x_5297_ = lean_array_push(v_log_5240_, v___x_5295_);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5297_);
v___x_5299_ = v___x_5290_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5301_, 1, v_trace_5243_);
lean_ctor_set(v_reuseFailAlloc_5301_, 2, v_buildTime_5244_);
lean_ctor_set_uint8(v_reuseFailAlloc_5301_, sizeof(void*)*3, v_action_5241_);
lean_ctor_set_uint8(v_reuseFailAlloc_5301_, sizeof(void*)*3 + 1, v_wantsRebuild_5242_);
v___x_5299_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; 
v___x_5300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5296_);
lean_ctor_set(v___x_5300_, 1, v___x_5299_);
return v___x_5300_;
}
}
}
}
else
{
lean_object* v___x_5306_; 
lean_dec_ref(v_val_5226_);
v___x_5306_ = l_Lake_computeArtifact___redArg(v_file_5221_, v_ext_5222_, v_text_5223_, v___y_5234_, v___y_5235_);
return v___x_5306_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5307_ = _args[0];
lean_object* v_file_5308_ = _args[1];
lean_object* v_ext_5309_ = _args[2];
lean_object* v_text_5310_ = _args[3];
lean_object* v_exe_5311_ = _args[4];
lean_object* v___y_5312_ = _args[5];
lean_object* v_val_5313_ = _args[6];
lean_object* v_hash_5314_ = _args[7];
lean_object* v_a_5315_ = _args[8];
lean_object* v_____r_5316_ = _args[9];
lean_object* v___y_5317_ = _args[10];
lean_object* v___y_5318_ = _args[11];
lean_object* v___y_5319_ = _args[12];
lean_object* v___y_5320_ = _args[13];
lean_object* v___y_5321_ = _args[14];
lean_object* v___y_5322_ = _args[15];
lean_object* v___y_5323_ = _args[16];
_start:
{
uint8_t v_a_299371__boxed_5324_; uint8_t v_text_boxed_5325_; uint8_t v_exe_boxed_5326_; uint8_t v___y_299372__boxed_5327_; uint64_t v_hash_boxed_5328_; uint8_t v_a_299374__boxed_5329_; lean_object* v_res_5330_; 
v_a_299371__boxed_5324_ = lean_unbox(v_a_5307_);
v_text_boxed_5325_ = lean_unbox(v_text_5310_);
v_exe_boxed_5326_ = lean_unbox(v_exe_5311_);
v___y_299372__boxed_5327_ = lean_unbox(v___y_5312_);
v_hash_boxed_5328_ = lean_unbox_uint64(v_hash_5314_);
lean_dec_ref(v_hash_5314_);
v_a_299374__boxed_5329_ = lean_unbox(v_a_5315_);
v_res_5330_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_299371__boxed_5324_, v_file_5308_, v_ext_5309_, v_text_boxed_5325_, v_exe_boxed_5326_, v___y_299372__boxed_5327_, v_val_5313_, v_hash_boxed_5328_, v_a_299374__boxed_5329_, v_____r_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5331_, lean_object* v_build_5332_, uint8_t v_text_5333_, lean_object* v_ext_5334_, uint8_t v_restore_5335_, uint8_t v_exe_5336_, uint8_t v_platformIndependent_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_){
_start:
{
lean_object* v_log_5345_; uint8_t v_action_5346_; uint8_t v_wantsRebuild_5347_; lean_object* v_trace_5348_; lean_object* v_buildTime_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5610_; 
v_log_5345_ = lean_ctor_get(v_a_5343_, 0);
v_action_5346_ = lean_ctor_get_uint8(v_a_5343_, sizeof(void*)*3);
v_wantsRebuild_5347_ = lean_ctor_get_uint8(v_a_5343_, sizeof(void*)*3 + 1);
v_trace_5348_ = lean_ctor_get(v_a_5343_, 1);
v_buildTime_5349_ = lean_ctor_get(v_a_5343_, 2);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_a_5343_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5351_ = v_a_5343_;
v_isShared_5352_ = v_isSharedCheck_5610_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_buildTime_5349_);
lean_inc(v_trace_5348_);
lean_inc(v_log_5345_);
lean_dec(v_a_5343_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5610_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v_art_5356_; lean_object* v___y_5357_; lean_object* v___y_5373_; lean_object* v_log_5374_; uint8_t v_action_5375_; uint8_t v_wantsRebuild_5376_; lean_object* v_buildTime_5377_; lean_object* v___x_5383_; 
v___x_5353_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5331_);
v___x_5354_ = lean_string_append(v_file_5331_, v___x_5353_);
lean_inc_ref(v___x_5354_);
v___x_5383_ = l_Lake_readTraceFile(v___x_5354_, v_log_5345_);
if (lean_obj_tag(v___x_5383_) == 0)
{
if (lean_obj_tag(v_a_5339_) == 1)
{
lean_object* v_a_5384_; lean_object* v_a_5385_; lean_object* v_val_5386_; uint64_t v_hash_5387_; lean_object* v_mtime_5388_; uint8_t v___y_5390_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v___y_5393_; lean_object* v___y_5394_; uint8_t v___y_5395_; lean_object* v___y_5396_; lean_object* v___y_5397_; lean_object* v___y_5398_; lean_object* v_wsIdx_5402_; lean_object* v_config_5403_; lean_object* v_a_5405_; lean_object* v_a_5406_; lean_object* v___y_5436_; lean_object* v_enableArtifactCache_x3f_5439_; lean_object* v_restoreAllArtifacts_x3f_5440_; uint8_t v___y_5442_; lean_object* v___y_5443_; uint8_t v___y_5444_; uint8_t v___y_5483_; uint8_t v___y_5484_; uint8_t v_a_5485_; lean_object* v_a_5486_; uint8_t v___y_5488_; lean_object* v_a_5489_; uint8_t v___y_5506_; uint8_t v_a_5507_; lean_object* v_a_5508_; lean_object* v_a_5511_; uint8_t v_a_5543_; lean_object* v_a_5544_; lean_object* v___x_5560_; 
v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_a_5384_);
v_a_5385_ = lean_ctor_get(v___x_5383_, 1);
lean_inc(v_a_5385_);
lean_dec_ref_known(v___x_5383_, 2);
v_val_5386_ = lean_ctor_get(v_a_5339_, 0);
v_hash_5387_ = lean_ctor_get_uint64(v_trace_5348_, sizeof(void*)*3);
v_mtime_5388_ = lean_ctor_get(v_trace_5348_, 2);
v_wsIdx_5402_ = lean_ctor_get(v_val_5386_, 0);
v_config_5403_ = lean_ctor_get(v_val_5386_, 6);
v_enableArtifactCache_x3f_5439_ = lean_ctor_get(v_config_5403_, 24);
v_restoreAllArtifacts_x3f_5440_ = lean_ctor_get(v_config_5403_, 25);
lean_inc_ref(v_trace_5348_);
v___x_5560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5560_, 0, v_a_5385_);
lean_ctor_set(v___x_5560_, 1, v_trace_5348_);
lean_ctor_set(v___x_5560_, 2, v_buildTime_5349_);
lean_ctor_set_uint8(v___x_5560_, sizeof(void*)*3, v_action_5346_);
lean_ctor_set_uint8(v___x_5560_, sizeof(void*)*3 + 1, v_wantsRebuild_5347_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5439_) == 0)
{
lean_object* v_toContext_5561_; lean_object* v_lakeEnv_5562_; lean_object* v_enableArtifactCache_x3f_5563_; 
v_toContext_5561_ = lean_ctor_get(v_a_5342_, 1);
v_lakeEnv_5562_ = lean_ctor_get(v_toContext_5561_, 0);
v_enableArtifactCache_x3f_5563_ = lean_ctor_get(v_lakeEnv_5562_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5563_) == 0)
{
lean_object* v_packages_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v_config_5567_; lean_object* v_enableArtifactCache_x3f_5568_; 
v_packages_5564_ = lean_ctor_get(v_toContext_5561_, 4);
v___x_5565_ = lean_unsigned_to_nat(0u);
v___x_5566_ = lean_array_fget_borrowed(v_packages_5564_, v___x_5565_);
v_config_5567_ = lean_ctor_get(v___x_5566_, 6);
v_enableArtifactCache_x3f_5568_ = lean_ctor_get(v_config_5567_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5568_) == 0)
{
v_a_5511_ = v___x_5560_;
goto v___jp_5510_;
}
else
{
lean_object* v_val_5569_; uint8_t v___x_5570_; 
v_val_5569_ = lean_ctor_get(v_enableArtifactCache_x3f_5568_, 0);
v___x_5570_ = lean_unbox(v_val_5569_);
v_a_5543_ = v___x_5570_;
v_a_5544_ = v___x_5560_;
goto v___jp_5542_;
}
}
else
{
lean_object* v_val_5571_; uint8_t v___x_5572_; 
v_val_5571_ = lean_ctor_get(v_enableArtifactCache_x3f_5563_, 0);
v___x_5572_ = lean_unbox(v_val_5571_);
v_a_5543_ = v___x_5572_;
v_a_5544_ = v___x_5560_;
goto v___jp_5542_;
}
}
else
{
lean_object* v_val_5573_; uint8_t v___x_5574_; 
v_val_5573_ = lean_ctor_get(v_enableArtifactCache_x3f_5439_, 0);
v___x_5574_ = lean_unbox(v_val_5573_);
v_a_5543_ = v___x_5574_;
v_a_5544_ = v___x_5560_;
goto v___jp_5542_;
}
v___jp_5389_:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_dec_ref(v___y_5397_);
v___x_5399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5399_, 0, v___y_5398_);
v___x_5400_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5387_, v___x_5399_, v___y_5391_, v_platformIndependent_5337_);
v___x_5401_ = lean_st_ref_set(v___y_5394_, v___x_5400_);
v___y_5373_ = v___y_5393_;
v_log_5374_ = v___y_5396_;
v_action_5375_ = v___y_5395_;
v_wantsRebuild_5376_ = v___y_5390_;
v_buildTime_5377_ = v___y_5392_;
goto v___jp_5372_;
}
v___jp_5404_:
{
lean_object* v___x_5407_; uint8_t v___x_5408_; 
v___x_5407_ = lean_unsigned_to_nat(0u);
v___x_5408_ = lean_nat_dec_eq(v_wsIdx_5402_, v___x_5407_);
if (v___x_5408_ == 0)
{
lean_object* v_log_5409_; uint8_t v_action_5410_; uint8_t v_wantsRebuild_5411_; lean_object* v_buildTime_5412_; 
v_log_5409_ = lean_ctor_get(v_a_5406_, 0);
lean_inc_ref(v_log_5409_);
v_action_5410_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3);
v_wantsRebuild_5411_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3 + 1);
v_buildTime_5412_ = lean_ctor_get(v_a_5406_, 2);
lean_inc(v_buildTime_5412_);
lean_dec_ref(v_a_5406_);
v___y_5373_ = v_a_5405_;
v_log_5374_ = v_log_5409_;
v_action_5375_ = v_action_5410_;
v_wantsRebuild_5376_ = v_wantsRebuild_5411_;
v_buildTime_5377_ = v_buildTime_5412_;
goto v___jp_5372_;
}
else
{
lean_object* v_outputsRef_x3f_5413_; 
v_outputsRef_x3f_5413_ = lean_ctor_get(v_a_5342_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5413_) == 1)
{
lean_object* v_log_5414_; uint8_t v_action_5415_; uint8_t v_wantsRebuild_5416_; lean_object* v_trace_5417_; lean_object* v_buildTime_5418_; lean_object* v_val_5419_; lean_object* v___x_5420_; lean_object* v_descr_5421_; uint64_t v_hash_5422_; lean_object* v_ext_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; 
v_log_5414_ = lean_ctor_get(v_a_5406_, 0);
lean_inc_ref(v_log_5414_);
v_action_5415_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3);
v_wantsRebuild_5416_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3 + 1);
v_trace_5417_ = lean_ctor_get(v_a_5406_, 1);
lean_inc_ref(v_trace_5417_);
v_buildTime_5418_ = lean_ctor_get(v_a_5406_, 2);
lean_inc(v_buildTime_5418_);
lean_dec_ref(v_a_5406_);
v_val_5419_ = lean_ctor_get(v_outputsRef_x3f_5413_, 0);
v___x_5420_ = lean_st_ref_take(v_val_5419_);
v_descr_5421_ = lean_ctor_get(v_a_5405_, 0);
v_hash_5422_ = lean_ctor_get_uint64(v_descr_5421_, sizeof(void*)*1);
v_ext_5423_ = lean_ctor_get(v_descr_5421_, 0);
v___x_5424_ = lean_string_utf8_byte_size(v_ext_5423_);
v___x_5425_ = lean_nat_dec_eq(v___x_5424_, v___x_5407_);
if (v___x_5425_ == 0)
{
lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5426_ = l_Lake_lowerHexUInt64(v_hash_5422_);
v___x_5427_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5428_ = lean_string_append(v___x_5426_, v___x_5427_);
v___x_5429_ = lean_string_append(v___x_5428_, v_ext_5423_);
v___y_5390_ = v_wantsRebuild_5416_;
v___y_5391_ = v___x_5420_;
v___y_5392_ = v_buildTime_5418_;
v___y_5393_ = v_a_5405_;
v___y_5394_ = v_val_5419_;
v___y_5395_ = v_action_5415_;
v___y_5396_ = v_log_5414_;
v___y_5397_ = v_trace_5417_;
v___y_5398_ = v___x_5429_;
goto v___jp_5389_;
}
else
{
lean_object* v___x_5430_; 
v___x_5430_ = l_Lake_lowerHexUInt64(v_hash_5422_);
v___y_5390_ = v_wantsRebuild_5416_;
v___y_5391_ = v___x_5420_;
v___y_5392_ = v_buildTime_5418_;
v___y_5393_ = v_a_5405_;
v___y_5394_ = v_val_5419_;
v___y_5395_ = v_action_5415_;
v___y_5396_ = v_log_5414_;
v___y_5397_ = v_trace_5417_;
v___y_5398_ = v___x_5430_;
goto v___jp_5389_;
}
}
else
{
lean_object* v_log_5431_; uint8_t v_action_5432_; uint8_t v_wantsRebuild_5433_; lean_object* v_buildTime_5434_; 
v_log_5431_ = lean_ctor_get(v_a_5406_, 0);
lean_inc_ref(v_log_5431_);
v_action_5432_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3);
v_wantsRebuild_5433_ = lean_ctor_get_uint8(v_a_5406_, sizeof(void*)*3 + 1);
v_buildTime_5434_ = lean_ctor_get(v_a_5406_, 2);
lean_inc(v_buildTime_5434_);
lean_dec_ref(v_a_5406_);
v___y_5373_ = v_a_5405_;
v_log_5374_ = v_log_5431_;
v_action_5375_ = v_action_5432_;
v_wantsRebuild_5376_ = v_wantsRebuild_5433_;
v_buildTime_5377_ = v_buildTime_5434_;
goto v___jp_5372_;
}
}
}
v___jp_5435_:
{
if (lean_obj_tag(v___y_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v_a_5438_; 
v_a_5437_ = lean_ctor_get(v___y_5436_, 0);
lean_inc(v_a_5437_);
v_a_5438_ = lean_ctor_get(v___y_5436_, 1);
lean_inc(v_a_5438_);
lean_dec_ref_known(v___y_5436_, 2);
v_a_5405_ = v_a_5437_;
v_a_5406_ = v_a_5438_;
goto v___jp_5404_;
}
else
{
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
return v___y_5436_;
}
}
v___jp_5441_:
{
lean_object* v___x_5445_; 
lean_inc_ref(v_a_5338_);
lean_inc_ref(v___x_5354_);
lean_inc_ref(v_file_5331_);
lean_inc(v_val_5386_);
lean_inc(v_a_5384_);
v___x_5445_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5336_, v_hash_5387_, v_a_5384_, v_val_5386_, v_file_5331_, v___x_5354_, v___y_5444_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v___y_5443_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v_a_5446_; 
v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_a_5446_);
if (lean_obj_tag(v_a_5446_) == 1)
{
lean_object* v_a_5447_; lean_object* v_val_5448_; 
lean_dec(v_a_5384_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5447_ = lean_ctor_get(v___x_5445_, 1);
lean_inc(v_a_5447_);
lean_dec_ref_known(v___x_5445_, 2);
v_val_5448_ = lean_ctor_get(v_a_5446_, 0);
lean_inc(v_val_5448_);
lean_dec_ref_known(v_a_5446_, 1);
v_a_5405_ = v_val_5448_;
v_a_5406_ = v_a_5447_;
goto v___jp_5404_;
}
else
{
lean_object* v_a_5449_; lean_object* v___x_5450_; 
lean_dec(v_a_5446_);
v_a_5449_ = lean_ctor_get(v___x_5445_, 1);
lean_inc(v_a_5449_);
lean_dec_ref_known(v___x_5445_, 2);
v___x_5450_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5338_, v_file_5331_, v_trace_5348_, v_a_5384_, v_mtime_5388_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5449_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v_a_5452_; uint8_t v___x_5453_; uint8_t v___x_5454_; uint8_t v___x_5455_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_a_5451_);
v_a_5452_ = lean_ctor_get(v___x_5450_, 1);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___x_5450_, 2);
v___x_5453_ = 0;
v___x_5454_ = lean_unbox(v_a_5451_);
v___x_5455_ = l_Lake_instDecidableEqOutputStatus(v___x_5454_, v___x_5453_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; 
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_build_5332_);
v___x_5456_ = lean_box(0);
v___x_5457_ = lean_unbox(v_a_5451_);
lean_dec(v_a_5451_);
lean_inc(v_val_5386_);
v___x_5458_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5457_, v_file_5331_, v_ext_5334_, v_text_5333_, v_exe_5336_, v___y_5444_, v_val_5386_, v_hash_5387_, v___y_5442_, v___x_5456_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5452_);
lean_dec_ref(v_a_5338_);
v___y_5436_ = v___x_5458_;
goto v___jp_5435_;
}
else
{
lean_object* v___x_5459_; 
lean_inc_ref(v_a_5338_);
lean_inc_ref(v___x_5354_);
lean_inc_ref(v_ext_5334_);
lean_inc_ref(v_file_5331_);
v___x_5459_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5331_, v_build_5332_, v_text_5333_, v_ext_5334_, v_trace_5348_, v___x_5354_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5452_);
lean_dec_ref(v_trace_5348_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5461_; uint8_t v___x_5462_; lean_object* v___x_5463_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 1);
lean_inc(v_a_5460_);
lean_dec_ref_known(v___x_5459_, 2);
v___x_5461_ = lean_box(0);
v___x_5462_ = lean_unbox(v_a_5451_);
lean_dec(v_a_5451_);
lean_inc(v_val_5386_);
v___x_5463_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5462_, v_file_5331_, v_ext_5334_, v_text_5333_, v_exe_5336_, v___y_5444_, v_val_5386_, v_hash_5387_, v___y_5442_, v___x_5461_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5460_);
lean_dec_ref(v_a_5338_);
v___y_5436_ = v___x_5463_;
goto v___jp_5435_;
}
else
{
lean_dec(v_a_5451_);
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_file_5331_);
return v___x_5459_;
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5472_; 
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5464_ = lean_ctor_get(v___x_5450_, 0);
v_a_5465_ = lean_ctor_get(v___x_5450_, 1);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5467_ = v___x_5450_;
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_inc(v_a_5464_);
lean_dec(v___x_5450_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5470_; 
if (v_isShared_5468_ == 0)
{
v___x_5470_ = v___x_5467_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5464_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_a_5465_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_dec(v_a_5384_);
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5473_ = lean_ctor_get(v___x_5445_, 0);
v_a_5474_ = lean_ctor_get(v___x_5445_, 1);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5445_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_inc(v_a_5473_);
lean_dec(v___x_5445_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5473_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
v___jp_5482_:
{
if (v_restore_5335_ == 0)
{
v___y_5442_ = v___y_5483_;
v___y_5443_ = v_a_5486_;
v___y_5444_ = v_a_5485_;
goto v___jp_5441_;
}
else
{
v___y_5442_ = v___y_5483_;
v___y_5443_ = v_a_5486_;
v___y_5444_ = v___y_5484_;
goto v___jp_5441_;
}
}
v___jp_5487_:
{
lean_object* v___x_5490_; 
lean_inc_ref(v_a_5338_);
lean_inc_ref(v___x_5354_);
lean_inc_ref(v_file_5331_);
lean_inc(v_val_5386_);
v___x_5490_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5336_, v_hash_5387_, v_a_5384_, v_val_5386_, v_file_5331_, v___x_5354_, v___y_5488_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5489_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
if (lean_obj_tag(v_a_5491_) == 1)
{
lean_object* v_a_5492_; lean_object* v_val_5493_; 
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5492_ = lean_ctor_get(v___x_5490_, 1);
lean_inc(v_a_5492_);
lean_dec_ref_known(v___x_5490_, 2);
v_val_5493_ = lean_ctor_get(v_a_5491_, 0);
lean_inc(v_val_5493_);
lean_dec_ref_known(v_a_5491_, 1);
v_a_5405_ = v_val_5493_;
v_a_5406_ = v_a_5492_;
goto v___jp_5404_;
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5495_; 
lean_dec(v_a_5491_);
v_a_5494_ = lean_ctor_get(v___x_5490_, 1);
lean_inc(v_a_5494_);
lean_dec_ref_known(v___x_5490_, 2);
lean_inc_ref(v___x_5354_);
v___x_5495_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5331_, v_build_5332_, v_text_5333_, v_ext_5334_, v_trace_5348_, v___x_5354_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5494_);
lean_dec_ref(v_trace_5348_);
v___y_5436_ = v___x_5495_;
goto v___jp_5435_;
}
}
else
{
lean_object* v_a_5496_; lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5504_; 
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5496_ = lean_ctor_get(v___x_5490_, 0);
v_a_5497_ = lean_ctor_get(v___x_5490_, 1);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5499_ = v___x_5490_;
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_inc(v_a_5496_);
lean_dec(v___x_5490_);
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
if (v_a_5507_ == 0)
{
lean_object* v___x_5509_; 
lean_dec(v_a_5384_);
lean_inc_ref(v___x_5354_);
v___x_5509_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5331_, v_build_5332_, v_text_5333_, v_ext_5334_, v_trace_5348_, v___x_5354_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5508_);
lean_dec_ref(v_trace_5348_);
v___y_5436_ = v___x_5509_;
goto v___jp_5435_;
}
else
{
v___y_5488_ = v___y_5506_;
v_a_5489_ = v_a_5508_;
goto v___jp_5487_;
}
}
v___jp_5510_:
{
lean_object* v___x_5512_; 
lean_inc(v_a_5384_);
v___x_5512_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5338_, v_file_5331_, v_trace_5348_, v_a_5384_, v_mtime_5388_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5511_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_a_5513_; lean_object* v_a_5514_; uint8_t v___x_5515_; uint8_t v___x_5516_; uint8_t v___x_5517_; 
v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_a_5513_);
v_a_5514_ = lean_ctor_get(v___x_5512_, 1);
lean_inc(v_a_5514_);
lean_dec_ref_known(v___x_5512_, 2);
v___x_5515_ = 0;
v___x_5516_ = lean_unbox(v_a_5513_);
lean_dec(v_a_5513_);
v___x_5517_ = l_Lake_instDecidableEqOutputStatus(v___x_5516_, v___x_5515_);
if (v___x_5517_ == 0)
{
lean_object* v___x_5518_; 
lean_dec(v_a_5384_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_build_5332_);
v___x_5518_ = l_Lake_computeArtifact___redArg(v_file_5331_, v_ext_5334_, v_text_5333_, v_a_5342_, v_a_5514_);
v___y_5436_ = v___x_5518_;
goto v___jp_5435_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5439_) == 0)
{
lean_object* v_toContext_5519_; lean_object* v_lakeEnv_5520_; lean_object* v_enableArtifactCache_x3f_5521_; 
v_toContext_5519_ = lean_ctor_get(v_a_5342_, 1);
v_lakeEnv_5520_ = lean_ctor_get(v_toContext_5519_, 0);
v_enableArtifactCache_x3f_5521_ = lean_ctor_get(v_lakeEnv_5520_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5521_) == 0)
{
lean_object* v_packages_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v_config_5525_; lean_object* v_enableArtifactCache_x3f_5526_; 
v_packages_5522_ = lean_ctor_get(v_toContext_5519_, 4);
v___x_5523_ = lean_unsigned_to_nat(0u);
v___x_5524_ = lean_array_fget_borrowed(v_packages_5522_, v___x_5523_);
v_config_5525_ = lean_ctor_get(v___x_5524_, 6);
v_enableArtifactCache_x3f_5526_ = lean_ctor_get(v_config_5525_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5526_) == 0)
{
v___y_5488_ = v___x_5517_;
v_a_5489_ = v_a_5514_;
goto v___jp_5487_;
}
else
{
lean_object* v_val_5527_; uint8_t v___x_5528_; 
v_val_5527_ = lean_ctor_get(v_enableArtifactCache_x3f_5526_, 0);
v___x_5528_ = lean_unbox(v_val_5527_);
v___y_5506_ = v___x_5517_;
v_a_5507_ = v___x_5528_;
v_a_5508_ = v_a_5514_;
goto v___jp_5505_;
}
}
else
{
lean_object* v_val_5529_; uint8_t v___x_5530_; 
v_val_5529_ = lean_ctor_get(v_enableArtifactCache_x3f_5521_, 0);
v___x_5530_ = lean_unbox(v_val_5529_);
v___y_5506_ = v___x_5517_;
v_a_5507_ = v___x_5530_;
v_a_5508_ = v_a_5514_;
goto v___jp_5505_;
}
}
else
{
lean_object* v_val_5531_; uint8_t v___x_5532_; 
v_val_5531_ = lean_ctor_get(v_enableArtifactCache_x3f_5439_, 0);
v___x_5532_ = lean_unbox(v_val_5531_);
v___y_5506_ = v___x_5517_;
v_a_5507_ = v___x_5532_;
v_a_5508_ = v_a_5514_;
goto v___jp_5505_;
}
}
}
else
{
lean_object* v_a_5533_; lean_object* v_a_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5541_; 
lean_dec(v_a_5384_);
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5533_ = lean_ctor_get(v___x_5512_, 0);
v_a_5534_ = lean_ctor_get(v___x_5512_, 1);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5536_ = v___x_5512_;
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_a_5534_);
lean_inc(v_a_5533_);
lean_dec(v___x_5512_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5533_);
lean_ctor_set(v_reuseFailAlloc_5540_, 1, v_a_5534_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
v___jp_5542_:
{
if (v_a_5543_ == 0)
{
v_a_5511_ = v_a_5544_;
goto v___jp_5510_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5440_) == 0)
{
lean_object* v_toContext_5545_; lean_object* v_lakeEnv_5546_; lean_object* v_restoreAllArtifacts_x3f_5547_; 
v_toContext_5545_ = lean_ctor_get(v_a_5342_, 1);
v_lakeEnv_5546_ = lean_ctor_get(v_toContext_5545_, 0);
v_restoreAllArtifacts_x3f_5547_ = lean_ctor_get(v_lakeEnv_5546_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5547_) == 0)
{
lean_object* v_packages_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v_config_5551_; lean_object* v_restoreAllArtifacts_x3f_5552_; 
v_packages_5548_ = lean_ctor_get(v_toContext_5545_, 4);
v___x_5549_ = lean_unsigned_to_nat(0u);
v___x_5550_ = lean_array_fget_borrowed(v_packages_5548_, v___x_5549_);
v_config_5551_ = lean_ctor_get(v___x_5550_, 6);
v_restoreAllArtifacts_x3f_5552_ = lean_ctor_get(v_config_5551_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5552_) == 0)
{
uint8_t v___x_5553_; 
v___x_5553_ = 0;
v___y_5483_ = v_a_5543_;
v___y_5484_ = v_a_5543_;
v_a_5485_ = v___x_5553_;
v_a_5486_ = v_a_5544_;
goto v___jp_5482_;
}
else
{
lean_object* v_val_5554_; uint8_t v___x_5555_; 
v_val_5554_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5552_, 0);
v___x_5555_ = lean_unbox(v_val_5554_);
v___y_5483_ = v_a_5543_;
v___y_5484_ = v_a_5543_;
v_a_5485_ = v___x_5555_;
v_a_5486_ = v_a_5544_;
goto v___jp_5482_;
}
}
else
{
lean_object* v_val_5556_; uint8_t v___x_5557_; 
v_val_5556_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5547_, 0);
v___x_5557_ = lean_unbox(v_val_5556_);
v___y_5483_ = v_a_5543_;
v___y_5484_ = v_a_5543_;
v_a_5485_ = v___x_5557_;
v_a_5486_ = v_a_5544_;
goto v___jp_5482_;
}
}
else
{
lean_object* v_val_5558_; uint8_t v___x_5559_; 
v_val_5558_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5440_, 0);
v___x_5559_ = lean_unbox(v_val_5558_);
v___y_5483_ = v_a_5543_;
v___y_5484_ = v_a_5543_;
v_a_5485_ = v___x_5559_;
v_a_5486_ = v_a_5544_;
goto v___jp_5482_;
}
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v_a_5576_; lean_object* v_mtime_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
lean_del_object(v___x_5351_);
v_a_5575_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_a_5575_);
v_a_5576_ = lean_ctor_get(v___x_5383_, 1);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5383_, 2);
v_mtime_5577_ = lean_ctor_get(v_trace_5348_, 2);
lean_inc_ref(v_trace_5348_);
v___x_5578_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5578_, 0, v_a_5576_);
lean_ctor_set(v___x_5578_, 1, v_trace_5348_);
lean_ctor_set(v___x_5578_, 2, v_buildTime_5349_);
lean_ctor_set_uint8(v___x_5578_, sizeof(void*)*3, v_action_5346_);
lean_ctor_set_uint8(v___x_5578_, sizeof(void*)*3 + 1, v_wantsRebuild_5347_);
v___x_5579_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5338_, v_file_5331_, v_trace_5348_, v_a_5575_, v_mtime_5577_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v___x_5578_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v_a_5581_; uint8_t v___x_5582_; uint8_t v___x_5583_; uint8_t v___x_5584_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5580_);
v_a_5581_ = lean_ctor_get(v___x_5579_, 1);
lean_inc(v_a_5581_);
lean_dec_ref_known(v___x_5579_, 2);
v___x_5582_ = 0;
v___x_5583_ = lean_unbox(v_a_5580_);
lean_dec(v_a_5580_);
v___x_5584_ = l_Lake_instDecidableEqOutputStatus(v___x_5583_, v___x_5582_);
if (v___x_5584_ == 0)
{
lean_object* v___x_5585_; 
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_build_5332_);
v___x_5585_ = l_Lake_computeArtifact___redArg(v_file_5331_, v_ext_5334_, v_text_5333_, v_a_5342_, v_a_5581_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v_a_5586_; lean_object* v_a_5587_; 
v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
lean_inc(v_a_5586_);
v_a_5587_ = lean_ctor_get(v___x_5585_, 1);
lean_inc(v_a_5587_);
lean_dec_ref_known(v___x_5585_, 2);
v_art_5356_ = v_a_5586_;
v___y_5357_ = v_a_5587_;
goto v___jp_5355_;
}
else
{
lean_dec_ref(v___x_5354_);
return v___x_5585_;
}
}
else
{
lean_object* v___x_5588_; 
lean_inc_ref(v___x_5354_);
v___x_5588_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5331_, v_build_5332_, v_text_5333_, v_ext_5334_, v_trace_5348_, v___x_5354_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5581_);
lean_dec_ref(v_trace_5348_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_a_5589_; lean_object* v_a_5590_; 
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_a_5589_);
v_a_5590_ = lean_ctor_get(v___x_5588_, 1);
lean_inc(v_a_5590_);
lean_dec_ref_known(v___x_5588_, 2);
v_art_5356_ = v_a_5589_;
v___y_5357_ = v_a_5590_;
goto v___jp_5355_;
}
else
{
lean_dec_ref(v___x_5354_);
return v___x_5588_;
}
}
}
else
{
lean_object* v_a_5591_; lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec_ref(v___x_5354_);
lean_dec_ref(v_trace_5348_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5591_ = lean_ctor_get(v___x_5579_, 0);
v_a_5592_ = lean_ctor_get(v___x_5579_, 1);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5579_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_inc(v_a_5591_);
lean_dec(v___x_5579_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5591_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
}
else
{
lean_object* v_a_5600_; lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5609_; 
lean_dec_ref(v___x_5354_);
lean_del_object(v___x_5351_);
lean_dec_ref(v_a_5338_);
lean_dec_ref(v_ext_5334_);
lean_dec_ref(v_build_5332_);
lean_dec_ref(v_file_5331_);
v_a_5600_ = lean_ctor_get(v___x_5383_, 0);
v_a_5601_ = lean_ctor_get(v___x_5383_, 1);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5603_ = v___x_5383_;
v_isShared_5604_ = v_isSharedCheck_5609_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_inc(v_a_5600_);
lean_dec(v___x_5383_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5609_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5605_; lean_object* v___x_5607_; 
v___x_5605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5605_, 0, v_a_5601_);
lean_ctor_set(v___x_5605_, 1, v_trace_5348_);
lean_ctor_set(v___x_5605_, 2, v_buildTime_5349_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*3, v_action_5346_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*3 + 1, v_wantsRebuild_5347_);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 1, v___x_5605_);
v___x_5607_ = v___x_5603_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5600_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v___x_5605_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
v___jp_5355_:
{
lean_object* v_log_5358_; uint8_t v_action_5359_; uint8_t v_wantsRebuild_5360_; lean_object* v_buildTime_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5370_; 
v_log_5358_ = lean_ctor_get(v___y_5357_, 0);
v_action_5359_ = lean_ctor_get_uint8(v___y_5357_, sizeof(void*)*3);
v_wantsRebuild_5360_ = lean_ctor_get_uint8(v___y_5357_, sizeof(void*)*3 + 1);
v_buildTime_5361_ = lean_ctor_get(v___y_5357_, 2);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___y_5357_);
if (v_isSharedCheck_5370_ == 0)
{
lean_object* v_unused_5371_; 
v_unused_5371_ = lean_ctor_get(v___y_5357_, 1);
lean_dec(v_unused_5371_);
v___x_5363_ = v___y_5357_;
v_isShared_5364_ = v_isSharedCheck_5370_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_buildTime_5361_);
lean_inc(v_log_5358_);
lean_dec(v___y_5357_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5370_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
v___x_5365_ = l_Lake_Artifact_trace(v_art_5356_);
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 1, v___x_5365_);
v___x_5367_ = v___x_5363_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_log_5358_);
lean_ctor_set(v_reuseFailAlloc_5369_, 1, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5369_, 2, v_buildTime_5361_);
lean_ctor_set_uint8(v_reuseFailAlloc_5369_, sizeof(void*)*3, v_action_5359_);
lean_ctor_set_uint8(v_reuseFailAlloc_5369_, sizeof(void*)*3 + 1, v_wantsRebuild_5360_);
v___x_5367_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5368_; 
v___x_5368_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5356_, v___x_5354_, v___x_5367_);
lean_dec_ref(v___x_5354_);
return v___x_5368_;
}
}
}
v___jp_5372_:
{
lean_object* v___x_5378_; lean_object* v___x_5380_; 
v___x_5378_ = l_Lake_Artifact_trace(v___y_5373_);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 2, v_buildTime_5377_);
lean_ctor_set(v___x_5351_, 1, v___x_5378_);
lean_ctor_set(v___x_5351_, 0, v_log_5374_);
v___x_5380_ = v___x_5351_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_log_5374_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5382_, 2, v_buildTime_5377_);
v___x_5380_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
lean_object* v___x_5381_; 
lean_ctor_set_uint8(v___x_5380_, sizeof(void*)*3, v_action_5375_);
lean_ctor_set_uint8(v___x_5380_, sizeof(void*)*3 + 1, v_wantsRebuild_5376_);
v___x_5381_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5373_, v___x_5354_, v___x_5380_);
lean_dec_ref(v___x_5354_);
return v___x_5381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5611_, lean_object* v_build_5612_, lean_object* v_text_5613_, lean_object* v_ext_5614_, lean_object* v_restore_5615_, lean_object* v_exe_5616_, lean_object* v_platformIndependent_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_){
_start:
{
uint8_t v_text_boxed_5625_; uint8_t v_restore_boxed_5626_; uint8_t v_exe_boxed_5627_; uint8_t v_platformIndependent_boxed_5628_; lean_object* v_res_5629_; 
v_text_boxed_5625_ = lean_unbox(v_text_5613_);
v_restore_boxed_5626_ = lean_unbox(v_restore_5615_);
v_exe_boxed_5627_ = lean_unbox(v_exe_5616_);
v_platformIndependent_boxed_5628_ = lean_unbox(v_platformIndependent_5617_);
v_res_5629_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5611_, v_build_5612_, v_text_boxed_5625_, v_ext_5614_, v_restore_boxed_5626_, v_exe_boxed_5627_, v_platformIndependent_boxed_5628_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_);
lean_dec_ref(v_a_5622_);
lean_dec(v_a_5621_);
lean_dec(v_a_5620_);
lean_dec(v_a_5619_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5631_, lean_object* v_build_5632_, lean_object* v_file_5633_, uint8_t v_text_5634_, lean_object* v_depInfo_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v___x_5643_; 
lean_inc_ref(v___y_5640_);
lean_inc(v___y_5639_);
lean_inc(v___y_5638_);
lean_inc(v___y_5637_);
lean_inc_ref(v___y_5636_);
v___x_5643_ = lean_apply_7(v_extraDepTrace_5631_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, lean_box(0));
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v_a_5644_; lean_object* v_a_5645_; lean_object* v_log_5646_; uint8_t v_action_5647_; uint8_t v_wantsRebuild_5648_; lean_object* v_trace_5649_; lean_object* v_buildTime_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5681_; 
v_a_5644_ = lean_ctor_get(v___x_5643_, 1);
lean_inc(v_a_5644_);
v_a_5645_ = lean_ctor_get(v___x_5643_, 0);
lean_inc(v_a_5645_);
lean_dec_ref_known(v___x_5643_, 2);
v_log_5646_ = lean_ctor_get(v_a_5644_, 0);
v_action_5647_ = lean_ctor_get_uint8(v_a_5644_, sizeof(void*)*3);
v_wantsRebuild_5648_ = lean_ctor_get_uint8(v_a_5644_, sizeof(void*)*3 + 1);
v_trace_5649_ = lean_ctor_get(v_a_5644_, 1);
v_buildTime_5650_ = lean_ctor_get(v_a_5644_, 2);
v_isSharedCheck_5681_ = !lean_is_exclusive(v_a_5644_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5652_ = v_a_5644_;
v_isShared_5653_ = v_isSharedCheck_5681_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_buildTime_5650_);
lean_inc(v_trace_5649_);
lean_inc(v_log_5646_);
lean_dec(v_a_5644_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5681_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5654_; lean_object* v___x_5656_; 
v___x_5654_ = l_Lake_BuildTrace_mix(v_trace_5649_, v_a_5645_);
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 1, v___x_5654_);
v___x_5656_ = v___x_5652_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_log_5646_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v___x_5654_);
lean_ctor_set(v_reuseFailAlloc_5680_, 2, v_buildTime_5650_);
lean_ctor_set_uint8(v_reuseFailAlloc_5680_, sizeof(void*)*3, v_action_5647_);
lean_ctor_set_uint8(v_reuseFailAlloc_5680_, sizeof(void*)*3 + 1, v_wantsRebuild_5648_);
v___x_5656_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; uint8_t v___x_5659_; lean_object* v___x_5660_; 
v___x_5657_ = lean_apply_1(v_build_5632_, v_depInfo_5635_);
v___x_5658_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5659_ = 0;
v___x_5660_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5633_, v___x_5657_, v_text_5634_, v___x_5658_, v___x_5659_, v___x_5659_, v___x_5659_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___x_5656_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5670_; 
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
v_a_5662_ = lean_ctor_get(v___x_5660_, 1);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5664_ = v___x_5660_;
v_isShared_5665_ = v_isSharedCheck_5670_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_inc(v_a_5661_);
lean_dec(v___x_5660_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5670_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v_path_5666_; lean_object* v___x_5668_; 
v_path_5666_ = lean_ctor_get(v_a_5661_, 1);
lean_inc_ref(v_path_5666_);
lean_dec(v_a_5661_);
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 0, v_path_5666_);
v___x_5668_ = v___x_5664_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_path_5666_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_a_5662_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
else
{
lean_object* v_a_5671_; lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
v_a_5671_ = lean_ctor_get(v___x_5660_, 0);
v_a_5672_ = lean_ctor_get(v___x_5660_, 1);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5660_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_inc(v_a_5671_);
lean_dec(v___x_5660_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5671_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v_a_5672_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
}
}
else
{
lean_object* v_a_5682_; lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
lean_dec_ref(v___y_5636_);
lean_dec(v_depInfo_5635_);
lean_dec_ref(v_file_5633_);
lean_dec_ref(v_build_5632_);
v_a_5682_ = lean_ctor_get(v___x_5643_, 0);
v_a_5683_ = lean_ctor_get(v___x_5643_, 1);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5643_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_inc(v_a_5682_);
lean_dec(v___x_5643_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5682_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5691_, lean_object* v_build_5692_, lean_object* v_file_5693_, lean_object* v_text_5694_, lean_object* v_depInfo_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
uint8_t v_text_boxed_5703_; lean_object* v_res_5704_; 
v_text_boxed_5703_ = lean_unbox(v_text_5694_);
v_res_5704_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5691_, v_build_5692_, v_file_5693_, v_text_boxed_5703_, v_depInfo_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec(v___y_5698_);
lean_dec(v___y_5697_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5705_, lean_object* v_dep_5706_, lean_object* v_build_5707_, lean_object* v_extraDepTrace_5708_, uint8_t v_text_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_){
_start:
{
lean_object* v___x_5717_; lean_object* v___f_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; uint8_t v___x_5721_; lean_object* v___x_5722_; 
v___x_5717_ = lean_box(v_text_5709_);
v___f_5718_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5718_, 0, v_extraDepTrace_5708_);
lean_closure_set(v___f_5718_, 1, v_build_5707_);
lean_closure_set(v___f_5718_, 2, v_file_5705_);
lean_closure_set(v___f_5718_, 3, v___x_5717_);
v___x_5719_ = l_Lake_instDataKindFilePath;
v___x_5720_ = lean_unsigned_to_nat(0u);
v___x_5721_ = 0;
v___x_5722_ = l_Lake_Job_mapM___redArg(v___x_5719_, v_dep_5706_, v___f_5718_, v___x_5720_, v___x_5721_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_);
return v___x_5722_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5723_, lean_object* v_dep_5724_, lean_object* v_build_5725_, lean_object* v_extraDepTrace_5726_, lean_object* v_text_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_){
_start:
{
uint8_t v_text_boxed_5735_; lean_object* v_res_5736_; 
v_text_boxed_5735_ = lean_unbox(v_text_5727_);
v_res_5736_ = l_Lake_buildFileAfterDep___redArg(v_file_5723_, v_dep_5724_, v_build_5725_, v_extraDepTrace_5726_, v_text_boxed_5735_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
lean_dec_ref(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec(v_a_5730_);
lean_dec(v_a_5729_);
return v_res_5736_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5737_, lean_object* v_file_5738_, lean_object* v_dep_5739_, lean_object* v_build_5740_, lean_object* v_extraDepTrace_5741_, uint8_t v_text_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v___x_5750_; lean_object* v___f_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; uint8_t v___x_5754_; lean_object* v___x_5755_; 
v___x_5750_ = lean_box(v_text_5742_);
v___f_5751_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5751_, 0, v_extraDepTrace_5741_);
lean_closure_set(v___f_5751_, 1, v_build_5740_);
lean_closure_set(v___f_5751_, 2, v_file_5738_);
lean_closure_set(v___f_5751_, 3, v___x_5750_);
v___x_5752_ = l_Lake_instDataKindFilePath;
v___x_5753_ = lean_unsigned_to_nat(0u);
v___x_5754_ = 0;
v___x_5755_ = l_Lake_Job_mapM___redArg(v___x_5752_, v_dep_5739_, v___f_5751_, v___x_5753_, v___x_5754_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_);
return v___x_5755_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5756_, lean_object* v_file_5757_, lean_object* v_dep_5758_, lean_object* v_build_5759_, lean_object* v_extraDepTrace_5760_, lean_object* v_text_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_){
_start:
{
uint8_t v_text_boxed_5769_; lean_object* v_res_5770_; 
v_text_boxed_5769_ = lean_unbox(v_text_5761_);
v_res_5770_ = l_Lake_buildFileAfterDep(v_00_u03b1_5756_, v_file_5757_, v_dep_5758_, v_build_5759_, v_extraDepTrace_5760_, v_text_boxed_5769_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
lean_dec_ref(v_a_5767_);
lean_dec_ref(v_a_5766_);
lean_dec(v_a_5765_);
lean_dec(v_a_5764_);
lean_dec(v_a_5763_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5771_){
_start:
{
lean_object* v___x_5773_; 
v___x_5773_ = l_Lake_computeBinFileHash(v_info_5771_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5775_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc(v_a_5774_);
lean_dec_ref_known(v___x_5773_, 1);
v___x_5775_ = lean_io_metadata(v_info_5771_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5787_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5787_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5787_ == 0)
{
v___x_5778_ = v___x_5775_;
v_isShared_5779_ = v_isSharedCheck_5787_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5775_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5787_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v_modified_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; uint64_t v___x_5783_; lean_object* v___x_5785_; 
v_modified_5780_ = lean_ctor_get(v_a_5776_, 1);
lean_inc_ref(v_modified_5780_);
lean_dec(v_a_5776_);
v___x_5781_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5782_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5782_, 0, v_info_5771_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
lean_ctor_set(v___x_5782_, 2, v_modified_5780_);
v___x_5783_ = lean_unbox_uint64(v_a_5774_);
lean_dec(v_a_5774_);
lean_ctor_set_uint64(v___x_5782_, sizeof(void*)*3, v___x_5783_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 0, v___x_5782_);
v___x_5785_ = v___x_5778_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5786_; 
v_reuseFailAlloc_5786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5786_, 0, v___x_5782_);
v___x_5785_ = v_reuseFailAlloc_5786_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
return v___x_5785_;
}
}
}
else
{
lean_object* v_a_5788_; lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5795_; 
lean_dec(v_a_5774_);
lean_dec_ref(v_info_5771_);
v_a_5788_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5795_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5795_ == 0)
{
v___x_5790_ = v___x_5775_;
v_isShared_5791_ = v_isSharedCheck_5795_;
goto v_resetjp_5789_;
}
else
{
lean_inc(v_a_5788_);
lean_dec(v___x_5775_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5795_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
lean_object* v___x_5793_; 
if (v_isShared_5791_ == 0)
{
v___x_5793_ = v___x_5790_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_a_5788_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
return v___x_5793_;
}
}
}
}
else
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5803_; 
lean_dec_ref(v_info_5771_);
v_a_5796_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5798_ = v___x_5773_;
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5773_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5801_; 
if (v_isShared_5799_ == 0)
{
v___x_5801_ = v___x_5798_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5796_);
v___x_5801_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
return v___x_5801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5804_, lean_object* v_a_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5804_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v_log_5815_; uint8_t v_action_5816_; uint8_t v_wantsRebuild_5817_; lean_object* v_trace_5818_; lean_object* v_buildTime_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5839_; 
v_log_5815_ = lean_ctor_get(v___y_5813_, 0);
v_action_5816_ = lean_ctor_get_uint8(v___y_5813_, sizeof(void*)*3);
v_wantsRebuild_5817_ = lean_ctor_get_uint8(v___y_5813_, sizeof(void*)*3 + 1);
v_trace_5818_ = lean_ctor_get(v___y_5813_, 1);
v_buildTime_5819_ = lean_ctor_get(v___y_5813_, 2);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___y_5813_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5821_ = v___y_5813_;
v_isShared_5822_ = v_isSharedCheck_5839_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_buildTime_5819_);
lean_inc(v_trace_5818_);
lean_inc(v_log_5815_);
lean_dec(v___y_5813_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5839_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5823_; 
lean_inc_ref(v_path_5807_);
v___x_5823_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5807_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v___x_5826_; 
lean_dec_ref(v_trace_5818_);
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
lean_inc(v_a_5824_);
lean_dec_ref_known(v___x_5823_, 1);
if (v_isShared_5822_ == 0)
{
lean_ctor_set(v___x_5821_, 1, v_a_5824_);
v___x_5826_ = v___x_5821_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_log_5815_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_a_5824_);
lean_ctor_set(v_reuseFailAlloc_5828_, 2, v_buildTime_5819_);
lean_ctor_set_uint8(v_reuseFailAlloc_5828_, sizeof(void*)*3, v_action_5816_);
lean_ctor_set_uint8(v_reuseFailAlloc_5828_, sizeof(void*)*3 + 1, v_wantsRebuild_5817_);
v___x_5826_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5827_; 
v___x_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5827_, 0, v_path_5807_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
return v___x_5827_;
}
}
else
{
lean_object* v_a_5829_; lean_object* v___x_5830_; uint8_t v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5836_; 
lean_dec_ref(v_path_5807_);
v_a_5829_ = lean_ctor_get(v___x_5823_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5823_, 1);
v___x_5830_ = lean_io_error_to_string(v_a_5829_);
v___x_5831_ = 3;
v___x_5832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set_uint8(v___x_5832_, sizeof(void*)*1, v___x_5831_);
v___x_5833_ = lean_array_get_size(v_log_5815_);
v___x_5834_ = lean_array_push(v_log_5815_, v___x_5832_);
if (v_isShared_5822_ == 0)
{
lean_ctor_set(v___x_5821_, 0, v___x_5834_);
v___x_5836_ = v___x_5821_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5838_, 1, v_trace_5818_);
lean_ctor_set(v_reuseFailAlloc_5838_, 2, v_buildTime_5819_);
lean_ctor_set_uint8(v_reuseFailAlloc_5838_, sizeof(void*)*3, v_action_5816_);
lean_ctor_set_uint8(v_reuseFailAlloc_5838_, sizeof(void*)*3 + 1, v_wantsRebuild_5817_);
v___x_5836_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
lean_object* v___x_5837_; 
v___x_5837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5833_);
lean_ctor_set(v___x_5837_, 1, v___x_5836_);
return v___x_5837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec_ref(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v___f_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___f_5857_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5857_, 0, v_path_5850_);
v___x_5858_ = l_Lake_instDataKindFilePath;
v___x_5859_ = lean_unsigned_to_nat(0u);
v___x_5860_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5861_ = l_Lake_Job_async___redArg(v___x_5858_, v___f_5857_, v___x_5859_, v___x_5860_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_);
return v___x_5861_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_, lean_object* v_a_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l_Lake_inputBinFile___redArg(v_path_5862_, v_a_5863_, v_a_5864_, v_a_5865_, v_a_5866_, v_a_5867_);
lean_dec_ref(v_a_5867_);
lean_dec(v_a_5866_);
lean_dec(v_a_5865_);
lean_dec(v_a_5864_);
return v_res_5869_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_){
_start:
{
lean_object* v___x_5878_; 
v___x_5878_ = l_Lake_inputBinFile___redArg(v_path_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
return v___x_5878_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v_res_5887_; 
v_res_5887_ = l_Lake_inputBinFile(v_path_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_);
lean_dec_ref(v_a_5885_);
lean_dec_ref(v_a_5884_);
lean_dec(v_a_5883_);
lean_dec(v_a_5882_);
lean_dec(v_a_5881_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5888_){
_start:
{
lean_object* v___x_5890_; 
v___x_5890_ = l_Lake_computeTextFileHash(v_info_5888_);
if (lean_obj_tag(v___x_5890_) == 0)
{
lean_object* v_a_5891_; lean_object* v___x_5892_; 
v_a_5891_ = lean_ctor_get(v___x_5890_, 0);
lean_inc(v_a_5891_);
lean_dec_ref_known(v___x_5890_, 1);
v___x_5892_ = lean_io_metadata(v_info_5888_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v_a_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5904_; 
v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5892_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5895_ = v___x_5892_;
v_isShared_5896_ = v_isSharedCheck_5904_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_a_5893_);
lean_dec(v___x_5892_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5904_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v_modified_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; uint64_t v___x_5900_; lean_object* v___x_5902_; 
v_modified_5897_ = lean_ctor_get(v_a_5893_, 1);
lean_inc_ref(v_modified_5897_);
lean_dec(v_a_5893_);
v___x_5898_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5899_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5899_, 0, v_info_5888_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
lean_ctor_set(v___x_5899_, 2, v_modified_5897_);
v___x_5900_ = lean_unbox_uint64(v_a_5891_);
lean_dec(v_a_5891_);
lean_ctor_set_uint64(v___x_5899_, sizeof(void*)*3, v___x_5900_);
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 0, v___x_5899_);
v___x_5902_ = v___x_5895_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v___x_5899_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec(v_a_5891_);
lean_dec_ref(v_info_5888_);
v_a_5905_ = lean_ctor_get(v___x_5892_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5892_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5892_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5892_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
lean_dec_ref(v_info_5888_);
v_a_5913_ = lean_ctor_get(v___x_5890_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5890_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5890_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5890_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5921_, lean_object* v_a_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5921_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_){
_start:
{
lean_object* v_log_5932_; uint8_t v_action_5933_; uint8_t v_wantsRebuild_5934_; lean_object* v_trace_5935_; lean_object* v_buildTime_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5956_; 
v_log_5932_ = lean_ctor_get(v___y_5930_, 0);
v_action_5933_ = lean_ctor_get_uint8(v___y_5930_, sizeof(void*)*3);
v_wantsRebuild_5934_ = lean_ctor_get_uint8(v___y_5930_, sizeof(void*)*3 + 1);
v_trace_5935_ = lean_ctor_get(v___y_5930_, 1);
v_buildTime_5936_ = lean_ctor_get(v___y_5930_, 2);
v_isSharedCheck_5956_ = !lean_is_exclusive(v___y_5930_);
if (v_isSharedCheck_5956_ == 0)
{
v___x_5938_ = v___y_5930_;
v_isShared_5939_ = v_isSharedCheck_5956_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_buildTime_5936_);
lean_inc(v_trace_5935_);
lean_inc(v_log_5932_);
lean_dec(v___y_5930_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5956_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5940_; 
lean_inc_ref(v_path_5924_);
v___x_5940_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5924_);
if (lean_obj_tag(v___x_5940_) == 0)
{
lean_object* v_a_5941_; lean_object* v___x_5943_; 
lean_dec_ref(v_trace_5935_);
v_a_5941_ = lean_ctor_get(v___x_5940_, 0);
lean_inc(v_a_5941_);
lean_dec_ref_known(v___x_5940_, 1);
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 1, v_a_5941_);
v___x_5943_ = v___x_5938_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_log_5932_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v_a_5941_);
lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_buildTime_5936_);
lean_ctor_set_uint8(v_reuseFailAlloc_5945_, sizeof(void*)*3, v_action_5933_);
lean_ctor_set_uint8(v_reuseFailAlloc_5945_, sizeof(void*)*3 + 1, v_wantsRebuild_5934_);
v___x_5943_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
lean_object* v___x_5944_; 
v___x_5944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5944_, 0, v_path_5924_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
return v___x_5944_;
}
}
else
{
lean_object* v_a_5946_; lean_object* v___x_5947_; uint8_t v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5953_; 
lean_dec_ref(v_path_5924_);
v_a_5946_ = lean_ctor_get(v___x_5940_, 0);
lean_inc(v_a_5946_);
lean_dec_ref_known(v___x_5940_, 1);
v___x_5947_ = lean_io_error_to_string(v_a_5946_);
v___x_5948_ = 3;
v___x_5949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set_uint8(v___x_5949_, sizeof(void*)*1, v___x_5948_);
v___x_5950_ = lean_array_get_size(v_log_5932_);
v___x_5951_ = lean_array_push(v_log_5932_, v___x_5949_);
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 0, v___x_5951_);
v___x_5953_ = v___x_5938_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5955_, 1, v_trace_5935_);
lean_ctor_set(v_reuseFailAlloc_5955_, 2, v_buildTime_5936_);
lean_ctor_set_uint8(v_reuseFailAlloc_5955_, sizeof(void*)*3, v_action_5933_);
lean_ctor_set_uint8(v_reuseFailAlloc_5955_, sizeof(void*)*3 + 1, v_wantsRebuild_5934_);
v___x_5953_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
lean_object* v___x_5954_; 
v___x_5954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5950_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
return v___x_5954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_){
_start:
{
lean_object* v_res_5965_; 
v_res_5965_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5957_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_);
lean_dec_ref(v___y_5962_);
lean_dec(v___y_5961_);
lean_dec(v___y_5960_);
lean_dec(v___y_5959_);
lean_dec_ref(v___y_5958_);
return v_res_5965_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
lean_object* v___f_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___f_5973_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5973_, 0, v_path_5966_);
v___x_5974_ = l_Lake_instDataKindFilePath;
v___x_5975_ = lean_unsigned_to_nat(0u);
v___x_5976_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5977_ = l_Lake_Job_async___redArg(v___x_5974_, v___f_5973_, v___x_5975_, v___x_5976_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lake_inputTextFile___redArg(v_path_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec(v_a_5981_);
lean_dec(v_a_5980_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = l_Lake_inputTextFile___redArg(v_path_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_){
_start:
{
lean_object* v_res_6003_; 
v_res_6003_ = l_Lake_inputTextFile(v_path_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, v_a_6001_);
lean_dec_ref(v_a_6001_);
lean_dec_ref(v_a_6000_);
lean_dec(v_a_5999_);
lean_dec(v_a_5998_);
lean_dec(v_a_5997_);
return v_res_6003_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_6004_, uint8_t v_text_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
if (v_text_6005_ == 0)
{
lean_object* v___x_6012_; 
v___x_6012_ = l_Lake_inputBinFile___redArg(v_path_6004_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
return v___x_6012_;
}
else
{
lean_object* v___x_6013_; 
v___x_6013_ = l_Lake_inputTextFile___redArg(v_path_6004_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
return v___x_6013_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_6014_, lean_object* v_text_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_){
_start:
{
uint8_t v_text_boxed_6022_; lean_object* v_res_6023_; 
v_text_boxed_6022_ = lean_unbox(v_text_6015_);
v_res_6023_ = l_Lake_inputFile___redArg(v_path_6014_, v_text_boxed_6022_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
lean_dec_ref(v_a_6020_);
lean_dec(v_a_6019_);
lean_dec(v_a_6018_);
lean_dec(v_a_6017_);
return v_res_6023_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_6024_, uint8_t v_text_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_){
_start:
{
if (v_text_6025_ == 0)
{
lean_object* v___x_6033_; 
v___x_6033_ = l_Lake_inputBinFile___redArg(v_path_6024_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
return v___x_6033_;
}
else
{
lean_object* v___x_6034_; 
v___x_6034_ = l_Lake_inputTextFile___redArg(v_path_6024_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
return v___x_6034_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_6035_, lean_object* v_text_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_, lean_object* v_a_6039_, lean_object* v_a_6040_, lean_object* v_a_6041_, lean_object* v_a_6042_, lean_object* v_a_6043_){
_start:
{
uint8_t v_text_boxed_6044_; lean_object* v_res_6045_; 
v_text_boxed_6044_ = lean_unbox(v_text_6036_);
v_res_6045_ = l_Lake_inputFile(v_path_6035_, v_text_boxed_6044_, v_a_6037_, v_a_6038_, v_a_6039_, v_a_6040_, v_a_6041_, v_a_6042_);
lean_dec_ref(v_a_6042_);
lean_dec_ref(v_a_6041_);
lean_dec(v_a_6040_);
lean_dec(v_a_6039_);
lean_dec(v_a_6038_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6046_){
_start:
{
uint8_t v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6048_ = 1;
v___x_6049_ = lean_box(v___x_6048_);
v___x_6050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6051_, lean_object* v___y_6052_){
_start:
{
lean_object* v_res_6053_; 
v_res_6053_ = l_Lake_inputDir___lam__0(v_x_6051_);
lean_dec_ref(v_x_6051_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6054_, lean_object* v_as_6055_, size_t v_i_6056_, size_t v_stop_6057_, lean_object* v_b_6058_, lean_object* v___y_6059_){
_start:
{
lean_object* v_a_6062_; lean_object* v_a_6063_; uint8_t v___x_6067_; 
v___x_6067_ = lean_usize_dec_eq(v_i_6056_, v_stop_6057_);
if (v___x_6067_ == 0)
{
lean_object* v___x_6068_; uint8_t v___x_6069_; 
v___x_6068_ = lean_array_uget_borrowed(v_as_6055_, v_i_6056_);
v___x_6069_ = l_System_FilePath_isDir(v___x_6068_);
if (v___x_6069_ == 0)
{
lean_object* v___x_6070_; uint8_t v___x_6071_; 
lean_inc_ref(v_filter_6054_);
lean_inc(v___x_6068_);
v___x_6070_ = lean_apply_1(v_filter_6054_, v___x_6068_);
v___x_6071_ = lean_unbox(v___x_6070_);
if (v___x_6071_ == 0)
{
v_a_6062_ = v_b_6058_;
v_a_6063_ = v___y_6059_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6072_; 
lean_inc(v___x_6068_);
v___x_6072_ = lean_array_push(v_b_6058_, v___x_6068_);
v_a_6062_ = v___x_6072_;
v_a_6063_ = v___y_6059_;
goto v___jp_6061_;
}
}
else
{
v_a_6062_ = v_b_6058_;
v_a_6063_ = v___y_6059_;
goto v___jp_6061_;
}
}
else
{
lean_object* v___x_6073_; 
lean_dec_ref(v_filter_6054_);
v___x_6073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6073_, 0, v_b_6058_);
lean_ctor_set(v___x_6073_, 1, v___y_6059_);
return v___x_6073_;
}
v___jp_6061_:
{
size_t v___x_6064_; size_t v___x_6065_; 
v___x_6064_ = ((size_t)1ULL);
v___x_6065_ = lean_usize_add(v_i_6056_, v___x_6064_);
v_i_6056_ = v___x_6065_;
v_b_6058_ = v_a_6062_;
v___y_6059_ = v_a_6063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6074_, lean_object* v_as_6075_, lean_object* v_i_6076_, lean_object* v_stop_6077_, lean_object* v_b_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_){
_start:
{
size_t v_i_boxed_6081_; size_t v_stop_boxed_6082_; lean_object* v_res_6083_; 
v_i_boxed_6081_ = lean_unbox_usize(v_i_6076_);
lean_dec(v_i_6076_);
v_stop_boxed_6082_ = lean_unbox_usize(v_stop_6077_);
lean_dec(v_stop_6077_);
v_res_6083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6074_, v_as_6075_, v_i_boxed_6081_, v_stop_boxed_6082_, v_b_6078_, v___y_6079_);
lean_dec_ref(v_as_6075_);
return v_res_6083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6084_, lean_object* v_pivot_6085_, lean_object* v_as_6086_, lean_object* v_i_6087_, lean_object* v_k_6088_){
_start:
{
uint8_t v___x_6089_; 
v___x_6089_ = lean_nat_dec_lt(v_k_6088_, v_hi_6084_);
if (v___x_6089_ == 0)
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
lean_dec(v_k_6088_);
v___x_6090_ = lean_array_fswap(v_as_6086_, v_i_6087_, v_hi_6084_);
v___x_6091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6091_, 0, v_i_6087_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
return v___x_6091_;
}
else
{
lean_object* v___x_6092_; uint8_t v___x_6093_; 
v___x_6092_ = lean_array_fget_borrowed(v_as_6086_, v_k_6088_);
v___x_6093_ = lean_string_dec_lt(v___x_6092_, v_pivot_6085_);
if (v___x_6093_ == 0)
{
lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6094_ = lean_unsigned_to_nat(1u);
v___x_6095_ = lean_nat_add(v_k_6088_, v___x_6094_);
lean_dec(v_k_6088_);
v_k_6088_ = v___x_6095_;
goto _start;
}
else
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6097_ = lean_array_fswap(v_as_6086_, v_i_6087_, v_k_6088_);
v___x_6098_ = lean_unsigned_to_nat(1u);
v___x_6099_ = lean_nat_add(v_i_6087_, v___x_6098_);
lean_dec(v_i_6087_);
v___x_6100_ = lean_nat_add(v_k_6088_, v___x_6098_);
lean_dec(v_k_6088_);
v_as_6086_ = v___x_6097_;
v_i_6087_ = v___x_6099_;
v_k_6088_ = v___x_6100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6102_, lean_object* v_pivot_6103_, lean_object* v_as_6104_, lean_object* v_i_6105_, lean_object* v_k_6106_){
_start:
{
lean_object* v_res_6107_; 
v_res_6107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6102_, v_pivot_6103_, v_as_6104_, v_i_6105_, v_k_6106_);
lean_dec_ref(v_pivot_6103_);
lean_dec(v_hi_6102_);
return v_res_6107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6108_, lean_object* v_as_6109_, lean_object* v_lo_6110_, lean_object* v_hi_6111_){
_start:
{
lean_object* v___y_6113_; uint8_t v___x_6123_; 
v___x_6123_ = lean_nat_dec_lt(v_lo_6110_, v_hi_6111_);
if (v___x_6123_ == 0)
{
lean_dec(v_lo_6110_);
return v_as_6109_;
}
else
{
lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v_mid_6126_; lean_object* v___y_6128_; lean_object* v___y_6134_; lean_object* v___x_6139_; lean_object* v___x_6140_; uint8_t v___x_6141_; 
v___x_6124_ = lean_nat_add(v_lo_6110_, v_hi_6111_);
v___x_6125_ = lean_unsigned_to_nat(1u);
v_mid_6126_ = lean_nat_shiftr(v___x_6124_, v___x_6125_);
lean_dec(v___x_6124_);
v___x_6139_ = lean_array_fget_borrowed(v_as_6109_, v_mid_6126_);
v___x_6140_ = lean_array_fget_borrowed(v_as_6109_, v_lo_6110_);
v___x_6141_ = lean_string_dec_lt(v___x_6139_, v___x_6140_);
if (v___x_6141_ == 0)
{
v___y_6134_ = v_as_6109_;
goto v___jp_6133_;
}
else
{
lean_object* v___x_6142_; 
v___x_6142_ = lean_array_fswap(v_as_6109_, v_lo_6110_, v_mid_6126_);
v___y_6134_ = v___x_6142_;
goto v___jp_6133_;
}
v___jp_6127_:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; uint8_t v___x_6131_; 
v___x_6129_ = lean_array_fget_borrowed(v___y_6128_, v_mid_6126_);
v___x_6130_ = lean_array_fget_borrowed(v___y_6128_, v_hi_6111_);
v___x_6131_ = lean_string_dec_lt(v___x_6129_, v___x_6130_);
if (v___x_6131_ == 0)
{
lean_dec(v_mid_6126_);
v___y_6113_ = v___y_6128_;
goto v___jp_6112_;
}
else
{
lean_object* v___x_6132_; 
v___x_6132_ = lean_array_fswap(v___y_6128_, v_mid_6126_, v_hi_6111_);
lean_dec(v_mid_6126_);
v___y_6113_ = v___x_6132_;
goto v___jp_6112_;
}
}
v___jp_6133_:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; uint8_t v___x_6137_; 
v___x_6135_ = lean_array_fget_borrowed(v___y_6134_, v_hi_6111_);
v___x_6136_ = lean_array_fget_borrowed(v___y_6134_, v_lo_6110_);
v___x_6137_ = lean_string_dec_lt(v___x_6135_, v___x_6136_);
if (v___x_6137_ == 0)
{
v___y_6128_ = v___y_6134_;
goto v___jp_6127_;
}
else
{
lean_object* v___x_6138_; 
v___x_6138_ = lean_array_fswap(v___y_6134_, v_lo_6110_, v_hi_6111_);
v___y_6128_ = v___x_6138_;
goto v___jp_6127_;
}
}
}
v___jp_6112_:
{
lean_object* v_pivot_6114_; lean_object* v___x_6115_; lean_object* v_fst_6116_; lean_object* v_snd_6117_; uint8_t v___x_6118_; 
v_pivot_6114_ = lean_array_fget(v___y_6113_, v_hi_6111_);
lean_inc_n(v_lo_6110_, 2);
v___x_6115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6111_, v_pivot_6114_, v___y_6113_, v_lo_6110_, v_lo_6110_);
lean_dec(v_pivot_6114_);
v_fst_6116_ = lean_ctor_get(v___x_6115_, 0);
lean_inc(v_fst_6116_);
v_snd_6117_ = lean_ctor_get(v___x_6115_, 1);
lean_inc(v_snd_6117_);
lean_dec_ref(v___x_6115_);
v___x_6118_ = lean_nat_dec_le(v_hi_6111_, v_fst_6116_);
if (v___x_6118_ == 0)
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6119_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6108_, v_snd_6117_, v_lo_6110_, v_fst_6116_);
v___x_6120_ = lean_unsigned_to_nat(1u);
v___x_6121_ = lean_nat_add(v_fst_6116_, v___x_6120_);
lean_dec(v_fst_6116_);
v_as_6109_ = v___x_6119_;
v_lo_6110_ = v___x_6121_;
goto _start;
}
else
{
lean_dec(v_fst_6116_);
lean_dec(v_lo_6110_);
return v_snd_6117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6143_, lean_object* v_as_6144_, lean_object* v_lo_6145_, lean_object* v_hi_6146_){
_start:
{
lean_object* v_res_6147_; 
v_res_6147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6143_, v_as_6144_, v_lo_6145_, v_hi_6146_);
lean_dec(v_hi_6146_);
lean_dec(v_n_6143_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6150_, lean_object* v___f_6151_, lean_object* v_filter_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_){
_start:
{
lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6172_; lean_object* v___y_6173_; lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v_log_6178_; uint8_t v_action_6179_; uint8_t v_wantsRebuild_6180_; lean_object* v_trace_6181_; lean_object* v_buildTime_6182_; lean_object* v___x_6183_; 
v_log_6178_ = lean_ctor_get(v___y_6158_, 0);
v_action_6179_ = lean_ctor_get_uint8(v___y_6158_, sizeof(void*)*3);
v_wantsRebuild_6180_ = lean_ctor_get_uint8(v___y_6158_, sizeof(void*)*3 + 1);
v_trace_6181_ = lean_ctor_get(v___y_6158_, 1);
v_buildTime_6182_ = lean_ctor_get(v___y_6158_, 2);
v___x_6183_ = l_System_FilePath_walkDir(v_path_6150_, v___f_6151_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_object* v_a_6184_; lean_object* v___x_6185_; lean_object* v_a_6187_; lean_object* v_a_6188_; lean_object* v___y_6195_; lean_object* v___x_6198_; lean_object* v___x_6199_; uint8_t v___x_6200_; 
v_a_6184_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_a_6184_);
lean_dec_ref_known(v___x_6183_, 1);
v___x_6185_ = lean_unsigned_to_nat(0u);
v___x_6198_ = lean_array_get_size(v_a_6184_);
v___x_6199_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6200_ = lean_nat_dec_lt(v___x_6185_, v___x_6198_);
if (v___x_6200_ == 0)
{
lean_dec(v_a_6184_);
lean_dec_ref(v_filter_6152_);
v_a_6187_ = v___x_6199_;
v_a_6188_ = v___y_6158_;
goto v___jp_6186_;
}
else
{
uint8_t v___x_6201_; 
v___x_6201_ = lean_nat_dec_le(v___x_6198_, v___x_6198_);
if (v___x_6201_ == 0)
{
if (v___x_6200_ == 0)
{
lean_dec(v_a_6184_);
lean_dec_ref(v_filter_6152_);
v_a_6187_ = v___x_6199_;
v_a_6188_ = v___y_6158_;
goto v___jp_6186_;
}
else
{
size_t v___x_6202_; size_t v___x_6203_; lean_object* v___x_6204_; 
v___x_6202_ = ((size_t)0ULL);
v___x_6203_ = lean_usize_of_nat(v___x_6198_);
v___x_6204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6152_, v_a_6184_, v___x_6202_, v___x_6203_, v___x_6199_, v___y_6158_);
lean_dec(v_a_6184_);
v___y_6195_ = v___x_6204_;
goto v___jp_6194_;
}
}
else
{
size_t v___x_6205_; size_t v___x_6206_; lean_object* v___x_6207_; 
v___x_6205_ = ((size_t)0ULL);
v___x_6206_ = lean_usize_of_nat(v___x_6198_);
v___x_6207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6152_, v_a_6184_, v___x_6205_, v___x_6206_, v___x_6199_, v___y_6158_);
lean_dec(v_a_6184_);
v___y_6195_ = v___x_6207_;
goto v___jp_6194_;
}
}
v___jp_6186_:
{
lean_object* v___x_6189_; uint8_t v___x_6190_; 
v___x_6189_ = lean_array_get_size(v_a_6187_);
v___x_6190_ = lean_nat_dec_eq(v___x_6189_, v___x_6185_);
if (v___x_6190_ == 0)
{
lean_object* v___x_6191_; lean_object* v___x_6192_; uint8_t v___x_6193_; 
v___x_6191_ = lean_unsigned_to_nat(1u);
v___x_6192_ = lean_nat_sub(v___x_6189_, v___x_6191_);
v___x_6193_ = lean_nat_dec_le(v___x_6185_, v___x_6192_);
if (v___x_6193_ == 0)
{
lean_inc(v___x_6192_);
v___y_6172_ = v___x_6192_;
v___y_6173_ = v___x_6189_;
v___y_6174_ = v_a_6188_;
v___y_6175_ = v_a_6187_;
v___y_6176_ = v___x_6192_;
goto v___jp_6171_;
}
else
{
v___y_6172_ = v___x_6192_;
v___y_6173_ = v___x_6189_;
v___y_6174_ = v_a_6188_;
v___y_6175_ = v_a_6187_;
v___y_6176_ = v___x_6185_;
goto v___jp_6171_;
}
}
else
{
v___y_6161_ = v_a_6188_;
v___y_6162_ = v_a_6187_;
goto v___jp_6160_;
}
}
v___jp_6194_:
{
if (lean_obj_tag(v___y_6195_) == 0)
{
lean_object* v_a_6196_; lean_object* v_a_6197_; 
v_a_6196_ = lean_ctor_get(v___y_6195_, 0);
lean_inc(v_a_6196_);
v_a_6197_ = lean_ctor_get(v___y_6195_, 1);
lean_inc(v_a_6197_);
lean_dec_ref_known(v___y_6195_, 2);
v_a_6187_ = v_a_6196_;
v_a_6188_ = v_a_6197_;
goto v___jp_6186_;
}
else
{
return v___y_6195_;
}
}
}
else
{
lean_object* v___x_6209_; uint8_t v_isShared_6210_; uint8_t v_isSharedCheck_6221_; 
lean_inc(v_buildTime_6182_);
lean_inc_ref(v_trace_6181_);
lean_inc_ref(v_log_6178_);
lean_dec_ref(v_filter_6152_);
v_isSharedCheck_6221_ = !lean_is_exclusive(v___y_6158_);
if (v_isSharedCheck_6221_ == 0)
{
lean_object* v_unused_6222_; lean_object* v_unused_6223_; lean_object* v_unused_6224_; 
v_unused_6222_ = lean_ctor_get(v___y_6158_, 2);
lean_dec(v_unused_6222_);
v_unused_6223_ = lean_ctor_get(v___y_6158_, 1);
lean_dec(v_unused_6223_);
v_unused_6224_ = lean_ctor_get(v___y_6158_, 0);
lean_dec(v_unused_6224_);
v___x_6209_ = v___y_6158_;
v_isShared_6210_ = v_isSharedCheck_6221_;
goto v_resetjp_6208_;
}
else
{
lean_dec(v___y_6158_);
v___x_6209_ = lean_box(0);
v_isShared_6210_ = v_isSharedCheck_6221_;
goto v_resetjp_6208_;
}
v_resetjp_6208_:
{
lean_object* v_a_6211_; lean_object* v___x_6212_; uint8_t v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6218_; 
v_a_6211_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_a_6211_);
lean_dec_ref_known(v___x_6183_, 1);
v___x_6212_ = lean_io_error_to_string(v_a_6211_);
v___x_6213_ = 3;
v___x_6214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6214_, 0, v___x_6212_);
lean_ctor_set_uint8(v___x_6214_, sizeof(void*)*1, v___x_6213_);
v___x_6215_ = lean_array_get_size(v_log_6178_);
v___x_6216_ = lean_array_push(v_log_6178_, v___x_6214_);
if (v_isShared_6210_ == 0)
{
lean_ctor_set(v___x_6209_, 0, v___x_6216_);
v___x_6218_ = v___x_6209_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6216_);
lean_ctor_set(v_reuseFailAlloc_6220_, 1, v_trace_6181_);
lean_ctor_set(v_reuseFailAlloc_6220_, 2, v_buildTime_6182_);
lean_ctor_set_uint8(v_reuseFailAlloc_6220_, sizeof(void*)*3, v_action_6179_);
lean_ctor_set_uint8(v_reuseFailAlloc_6220_, sizeof(void*)*3 + 1, v_wantsRebuild_6180_);
v___x_6218_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
lean_object* v___x_6219_; 
v___x_6219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6215_);
lean_ctor_set(v___x_6219_, 1, v___x_6218_);
return v___x_6219_;
}
}
}
v___jp_6160_:
{
lean_object* v___x_6163_; 
v___x_6163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___y_6162_);
lean_ctor_set(v___x_6163_, 1, v___y_6161_);
return v___x_6163_;
}
v___jp_6164_:
{
lean_object* v___x_6170_; 
v___x_6170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6166_, v___y_6168_, v___y_6165_, v___y_6169_);
lean_dec(v___y_6169_);
lean_dec(v___y_6166_);
v___y_6161_ = v___y_6167_;
v___y_6162_ = v___x_6170_;
goto v___jp_6160_;
}
v___jp_6171_:
{
uint8_t v___x_6177_; 
v___x_6177_ = lean_nat_dec_le(v___y_6176_, v___y_6172_);
if (v___x_6177_ == 0)
{
lean_dec(v___y_6172_);
lean_inc(v___y_6176_);
v___y_6165_ = v___y_6176_;
v___y_6166_ = v___y_6173_;
v___y_6167_ = v___y_6174_;
v___y_6168_ = v___y_6175_;
v___y_6169_ = v___y_6176_;
goto v___jp_6164_;
}
else
{
v___y_6165_ = v___y_6176_;
v___y_6166_ = v___y_6173_;
v___y_6167_ = v___y_6174_;
v___y_6168_ = v___y_6175_;
v___y_6169_ = v___y_6172_;
goto v___jp_6164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6225_, lean_object* v___f_6226_, lean_object* v_filter_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l_Lake_inputDir___lam__1(v_path_6225_, v___f_6226_, v_filter_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
lean_dec_ref(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6236_, size_t v_sz_6237_, size_t v_i_6238_, lean_object* v_bs_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_){
_start:
{
uint8_t v___x_6247_; 
v___x_6247_ = lean_usize_dec_lt(v_i_6238_, v_sz_6237_);
if (v___x_6247_ == 0)
{
lean_object* v___x_6248_; 
lean_dec_ref(v___y_6240_);
v___x_6248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6248_, 0, v_bs_6239_);
lean_ctor_set(v___x_6248_, 1, v___y_6245_);
return v___x_6248_;
}
else
{
lean_object* v_v_6249_; lean_object* v___x_6250_; lean_object* v_bs_x27_6251_; lean_object* v___y_6253_; 
v_v_6249_ = lean_array_uget(v_bs_6239_, v_i_6238_);
v___x_6250_ = lean_unsigned_to_nat(0u);
v_bs_x27_6251_ = lean_array_uset(v_bs_6239_, v_i_6238_, v___x_6250_);
if (v_text_6236_ == 0)
{
lean_object* v___x_6258_; 
lean_inc_ref(v___y_6240_);
v___x_6258_ = l_Lake_inputBinFile___redArg(v_v_6249_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_);
v___y_6253_ = v___x_6258_;
goto v___jp_6252_;
}
else
{
lean_object* v___x_6259_; 
lean_inc_ref(v___y_6240_);
v___x_6259_ = l_Lake_inputTextFile___redArg(v_v_6249_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_);
v___y_6253_ = v___x_6259_;
goto v___jp_6252_;
}
v___jp_6252_:
{
size_t v___x_6254_; size_t v___x_6255_; lean_object* v___x_6256_; 
v___x_6254_ = ((size_t)1ULL);
v___x_6255_ = lean_usize_add(v_i_6238_, v___x_6254_);
v___x_6256_ = lean_array_uset(v_bs_x27_6251_, v_i_6238_, v___y_6253_);
v_i_6238_ = v___x_6255_;
v_bs_6239_ = v___x_6256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6260_, lean_object* v_sz_6261_, lean_object* v_i_6262_, lean_object* v_bs_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_){
_start:
{
uint8_t v_text_boxed_6271_; size_t v_sz_boxed_6272_; size_t v_i_boxed_6273_; lean_object* v_res_6274_; 
v_text_boxed_6271_ = lean_unbox(v_text_6260_);
v_sz_boxed_6272_ = lean_unbox_usize(v_sz_6261_);
lean_dec(v_sz_6261_);
v_i_boxed_6273_ = lean_unbox_usize(v_i_6262_);
lean_dec(v_i_6262_);
v_res_6274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6271_, v_sz_boxed_6272_, v_i_boxed_6273_, v_bs_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_);
lean_dec_ref(v___y_6268_);
lean_dec(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec(v___y_6265_);
return v_res_6274_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6275_, lean_object* v_path_6276_, lean_object* v_ps_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_){
_start:
{
size_t v_sz_6285_; size_t v___x_6286_; lean_object* v___x_6287_; 
v_sz_6285_ = lean_array_size(v_ps_6277_);
v___x_6286_ = ((size_t)0ULL);
v___x_6287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6275_, v_sz_6285_, v___x_6286_, v_ps_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
if (lean_obj_tag(v___x_6287_) == 0)
{
lean_object* v_a_6288_; lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6297_; 
v_a_6288_ = lean_ctor_get(v___x_6287_, 0);
v_a_6289_ = lean_ctor_get(v___x_6287_, 1);
v_isSharedCheck_6297_ = !lean_is_exclusive(v___x_6287_);
if (v_isSharedCheck_6297_ == 0)
{
v___x_6291_ = v___x_6287_;
v_isShared_6292_ = v_isSharedCheck_6297_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_inc(v_a_6288_);
lean_dec(v___x_6287_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6297_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6293_; lean_object* v___x_6295_; 
v___x_6293_ = l_Lake_Job_collectArray___redArg(v_a_6288_, v_path_6276_);
lean_dec(v_a_6288_);
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 0, v___x_6293_);
v___x_6295_ = v___x_6291_;
goto v_reusejp_6294_;
}
else
{
lean_object* v_reuseFailAlloc_6296_; 
v_reuseFailAlloc_6296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6296_, 0, v___x_6293_);
lean_ctor_set(v_reuseFailAlloc_6296_, 1, v_a_6289_);
v___x_6295_ = v_reuseFailAlloc_6296_;
goto v_reusejp_6294_;
}
v_reusejp_6294_:
{
return v___x_6295_;
}
}
}
else
{
lean_object* v_a_6298_; lean_object* v_a_6299_; lean_object* v___x_6301_; uint8_t v_isShared_6302_; uint8_t v_isSharedCheck_6306_; 
lean_dec_ref(v_path_6276_);
v_a_6298_ = lean_ctor_get(v___x_6287_, 0);
v_a_6299_ = lean_ctor_get(v___x_6287_, 1);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6287_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6301_ = v___x_6287_;
v_isShared_6302_ = v_isSharedCheck_6306_;
goto v_resetjp_6300_;
}
else
{
lean_inc(v_a_6299_);
lean_inc(v_a_6298_);
lean_dec(v___x_6287_);
v___x_6301_ = lean_box(0);
v_isShared_6302_ = v_isSharedCheck_6306_;
goto v_resetjp_6300_;
}
v_resetjp_6300_:
{
lean_object* v___x_6304_; 
if (v_isShared_6302_ == 0)
{
v___x_6304_ = v___x_6301_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_a_6298_);
lean_ctor_set(v_reuseFailAlloc_6305_, 1, v_a_6299_);
v___x_6304_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
return v___x_6304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6307_, lean_object* v_path_6308_, lean_object* v_ps_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_){
_start:
{
uint8_t v_text_boxed_6317_; lean_object* v_res_6318_; 
v_text_boxed_6317_ = lean_unbox(v_text_6307_);
v_res_6318_ = l_Lake_inputDir___lam__2(v_text_boxed_6317_, v_path_6308_, v_ps_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
lean_dec_ref(v___y_6314_);
lean_dec(v___y_6313_);
lean_dec(v___y_6312_);
lean_dec(v___y_6311_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6320_, uint8_t v_text_6321_, lean_object* v_filter_6322_, lean_object* v_a_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_){
_start:
{
lean_object* v___f_6330_; lean_object* v___f_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___f_6337_; uint8_t v___x_6338_; lean_object* v___x_6339_; 
v___f_6330_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6320_);
v___f_6331_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6331_, 0, v_path_6320_);
lean_closure_set(v___f_6331_, 1, v___f_6330_);
lean_closure_set(v___f_6331_, 2, v_filter_6322_);
v___x_6332_ = lean_box(0);
v___x_6333_ = lean_unsigned_to_nat(0u);
v___x_6334_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6323_);
v___x_6335_ = l_Lake_Job_async___redArg(v___x_6332_, v___f_6331_, v___x_6333_, v___x_6334_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
v___x_6336_ = lean_box(v_text_6321_);
v___f_6337_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6337_, 0, v___x_6336_);
lean_closure_set(v___f_6337_, 1, v_path_6320_);
v___x_6338_ = 0;
v___x_6339_ = l_Lake_Job_bindM___redArg(v___x_6332_, v___x_6335_, v___f_6337_, v___x_6333_, v___x_6338_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_, v_a_6328_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6340_, lean_object* v_text_6341_, lean_object* v_filter_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_){
_start:
{
uint8_t v_text_boxed_6350_; lean_object* v_res_6351_; 
v_text_boxed_6350_ = lean_unbox(v_text_6341_);
v_res_6351_ = l_Lake_inputDir(v_path_6340_, v_text_boxed_6350_, v_filter_6342_, v_a_6343_, v_a_6344_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_);
lean_dec_ref(v_a_6348_);
lean_dec_ref(v_a_6347_);
lean_dec(v_a_6346_);
lean_dec(v_a_6345_);
lean_dec(v_a_6344_);
return v_res_6351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6352_, lean_object* v_as_6353_, lean_object* v_lo_6354_, lean_object* v_hi_6355_, lean_object* v_w_6356_, lean_object* v_hlo_6357_, lean_object* v_hhi_6358_){
_start:
{
lean_object* v___x_6359_; 
v___x_6359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6352_, v_as_6353_, v_lo_6354_, v_hi_6355_);
return v___x_6359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6360_, lean_object* v_as_6361_, lean_object* v_lo_6362_, lean_object* v_hi_6363_, lean_object* v_w_6364_, lean_object* v_hlo_6365_, lean_object* v_hhi_6366_){
_start:
{
lean_object* v_res_6367_; 
v_res_6367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6360_, v_as_6361_, v_lo_6362_, v_hi_6363_, v_w_6364_, v_hlo_6365_, v_hhi_6366_);
lean_dec(v_hi_6363_);
lean_dec(v_n_6360_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6368_, lean_object* v_as_6369_, size_t v_i_6370_, size_t v_stop_6371_, lean_object* v_b_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_){
_start:
{
lean_object* v___x_6380_; 
v___x_6380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6368_, v_as_6369_, v_i_6370_, v_stop_6371_, v_b_6372_, v___y_6378_);
return v___x_6380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6381_, lean_object* v_as_6382_, lean_object* v_i_6383_, lean_object* v_stop_6384_, lean_object* v_b_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_){
_start:
{
size_t v_i_boxed_6393_; size_t v_stop_boxed_6394_; lean_object* v_res_6395_; 
v_i_boxed_6393_ = lean_unbox_usize(v_i_6383_);
lean_dec(v_i_6383_);
v_stop_boxed_6394_ = lean_unbox_usize(v_stop_6384_);
lean_dec(v_stop_6384_);
v_res_6395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6381_, v_as_6382_, v_i_boxed_6393_, v_stop_boxed_6394_, v_b_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_);
lean_dec_ref(v___y_6390_);
lean_dec(v___y_6389_);
lean_dec(v___y_6388_);
lean_dec(v___y_6387_);
lean_dec_ref(v___y_6386_);
lean_dec_ref(v_as_6382_);
return v_res_6395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6396_, lean_object* v_lo_6397_, lean_object* v_hi_6398_, lean_object* v_hhi_6399_, lean_object* v_pivot_6400_, lean_object* v_as_6401_, lean_object* v_i_6402_, lean_object* v_k_6403_, lean_object* v_ilo_6404_, lean_object* v_ik_6405_, lean_object* v_w_6406_){
_start:
{
lean_object* v___x_6407_; 
v___x_6407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6398_, v_pivot_6400_, v_as_6401_, v_i_6402_, v_k_6403_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6408_, lean_object* v_lo_6409_, lean_object* v_hi_6410_, lean_object* v_hhi_6411_, lean_object* v_pivot_6412_, lean_object* v_as_6413_, lean_object* v_i_6414_, lean_object* v_k_6415_, lean_object* v_ilo_6416_, lean_object* v_ik_6417_, lean_object* v_w_6418_){
_start:
{
lean_object* v_res_6419_; 
v_res_6419_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6408_, v_lo_6409_, v_hi_6410_, v_hhi_6411_, v_pivot_6412_, v_as_6413_, v_i_6414_, v_k_6415_, v_ilo_6416_, v_ik_6417_, v_w_6418_);
lean_dec_ref(v_pivot_6412_);
lean_dec(v_hi_6410_);
lean_dec(v_lo_6409_);
lean_dec(v_n_6408_);
return v_res_6419_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6420_, lean_object* v_t_6421_){
_start:
{
uint64_t v___x_6422_; uint64_t v___x_6423_; uint64_t v___x_6424_; uint64_t v___x_6425_; 
v___x_6422_ = l_Lake_Hash_nil;
v___x_6423_ = lean_string_hash(v_t_6421_);
v___x_6424_ = lean_uint64_mix_hash(v___x_6422_, v___x_6423_);
v___x_6425_ = lean_uint64_mix_hash(v_ts_6420_, v___x_6424_);
return v___x_6425_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6426_, lean_object* v_t_6427_){
_start:
{
uint64_t v_ts_boxed_6428_; uint64_t v_res_6429_; lean_object* v_r_6430_; 
v_ts_boxed_6428_ = lean_unbox_uint64(v_ts_6426_);
lean_dec_ref(v_ts_6426_);
v_res_6429_ = l_Lake_buildO___lam__0(v_ts_boxed_6428_, v_t_6427_);
lean_dec_ref(v_t_6427_);
v_r_6430_ = lean_box_uint64(v_res_6429_);
return v_r_6430_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6431_, lean_object* v_srcFile_6432_, lean_object* v___x_6433_, lean_object* v_compiler_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_){
_start:
{
lean_object* v_log_6442_; uint8_t v_action_6443_; uint8_t v_wantsRebuild_6444_; lean_object* v_trace_6445_; lean_object* v_buildTime_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6475_; 
v_log_6442_ = lean_ctor_get(v___y_6440_, 0);
v_action_6443_ = lean_ctor_get_uint8(v___y_6440_, sizeof(void*)*3);
v_wantsRebuild_6444_ = lean_ctor_get_uint8(v___y_6440_, sizeof(void*)*3 + 1);
v_trace_6445_ = lean_ctor_get(v___y_6440_, 1);
v_buildTime_6446_ = lean_ctor_get(v___y_6440_, 2);
v_isSharedCheck_6475_ = !lean_is_exclusive(v___y_6440_);
if (v_isSharedCheck_6475_ == 0)
{
v___x_6448_ = v___y_6440_;
v_isShared_6449_ = v_isSharedCheck_6475_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_buildTime_6446_);
lean_inc(v_trace_6445_);
lean_inc(v_log_6442_);
lean_dec(v___y_6440_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6475_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6450_; 
v___x_6450_ = l_Lake_compileO(v_oFile_6431_, v_srcFile_6432_, v___x_6433_, v_compiler_6434_, v_log_6442_);
if (lean_obj_tag(v___x_6450_) == 0)
{
lean_object* v_a_6451_; lean_object* v_a_6452_; lean_object* v___x_6454_; uint8_t v_isShared_6455_; uint8_t v_isSharedCheck_6462_; 
v_a_6451_ = lean_ctor_get(v___x_6450_, 0);
v_a_6452_ = lean_ctor_get(v___x_6450_, 1);
v_isSharedCheck_6462_ = !lean_is_exclusive(v___x_6450_);
if (v_isSharedCheck_6462_ == 0)
{
v___x_6454_ = v___x_6450_;
v_isShared_6455_ = v_isSharedCheck_6462_;
goto v_resetjp_6453_;
}
else
{
lean_inc(v_a_6452_);
lean_inc(v_a_6451_);
lean_dec(v___x_6450_);
v___x_6454_ = lean_box(0);
v_isShared_6455_ = v_isSharedCheck_6462_;
goto v_resetjp_6453_;
}
v_resetjp_6453_:
{
lean_object* v___x_6457_; 
if (v_isShared_6449_ == 0)
{
lean_ctor_set(v___x_6448_, 0, v_a_6452_);
v___x_6457_ = v___x_6448_;
goto v_reusejp_6456_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6452_);
lean_ctor_set(v_reuseFailAlloc_6461_, 1, v_trace_6445_);
lean_ctor_set(v_reuseFailAlloc_6461_, 2, v_buildTime_6446_);
lean_ctor_set_uint8(v_reuseFailAlloc_6461_, sizeof(void*)*3, v_action_6443_);
lean_ctor_set_uint8(v_reuseFailAlloc_6461_, sizeof(void*)*3 + 1, v_wantsRebuild_6444_);
v___x_6457_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6456_;
}
v_reusejp_6456_:
{
lean_object* v___x_6459_; 
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 1, v___x_6457_);
v___x_6459_ = v___x_6454_;
goto v_reusejp_6458_;
}
else
{
lean_object* v_reuseFailAlloc_6460_; 
v_reuseFailAlloc_6460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6460_, 0, v_a_6451_);
lean_ctor_set(v_reuseFailAlloc_6460_, 1, v___x_6457_);
v___x_6459_ = v_reuseFailAlloc_6460_;
goto v_reusejp_6458_;
}
v_reusejp_6458_:
{
return v___x_6459_;
}
}
}
}
else
{
lean_object* v_a_6463_; lean_object* v_a_6464_; lean_object* v___x_6466_; uint8_t v_isShared_6467_; uint8_t v_isSharedCheck_6474_; 
v_a_6463_ = lean_ctor_get(v___x_6450_, 0);
v_a_6464_ = lean_ctor_get(v___x_6450_, 1);
v_isSharedCheck_6474_ = !lean_is_exclusive(v___x_6450_);
if (v_isSharedCheck_6474_ == 0)
{
v___x_6466_ = v___x_6450_;
v_isShared_6467_ = v_isSharedCheck_6474_;
goto v_resetjp_6465_;
}
else
{
lean_inc(v_a_6464_);
lean_inc(v_a_6463_);
lean_dec(v___x_6450_);
v___x_6466_ = lean_box(0);
v_isShared_6467_ = v_isSharedCheck_6474_;
goto v_resetjp_6465_;
}
v_resetjp_6465_:
{
lean_object* v___x_6469_; 
if (v_isShared_6449_ == 0)
{
lean_ctor_set(v___x_6448_, 0, v_a_6464_);
v___x_6469_ = v___x_6448_;
goto v_reusejp_6468_;
}
else
{
lean_object* v_reuseFailAlloc_6473_; 
v_reuseFailAlloc_6473_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6464_);
lean_ctor_set(v_reuseFailAlloc_6473_, 1, v_trace_6445_);
lean_ctor_set(v_reuseFailAlloc_6473_, 2, v_buildTime_6446_);
lean_ctor_set_uint8(v_reuseFailAlloc_6473_, sizeof(void*)*3, v_action_6443_);
lean_ctor_set_uint8(v_reuseFailAlloc_6473_, sizeof(void*)*3 + 1, v_wantsRebuild_6444_);
v___x_6469_ = v_reuseFailAlloc_6473_;
goto v_reusejp_6468_;
}
v_reusejp_6468_:
{
lean_object* v___x_6471_; 
if (v_isShared_6467_ == 0)
{
lean_ctor_set(v___x_6466_, 1, v___x_6469_);
v___x_6471_ = v___x_6466_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6463_);
lean_ctor_set(v_reuseFailAlloc_6472_, 1, v___x_6469_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
return v___x_6471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6476_, lean_object* v_srcFile_6477_, lean_object* v___x_6478_, lean_object* v_compiler_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_){
_start:
{
lean_object* v_res_6487_; 
v_res_6487_ = l_Lake_buildO___lam__1(v_oFile_6476_, v_srcFile_6477_, v___x_6478_, v_compiler_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_, v___y_6485_);
lean_dec_ref(v___y_6484_);
lean_dec(v___y_6483_);
lean_dec(v___y_6482_);
lean_dec(v___y_6481_);
lean_dec_ref(v___y_6480_);
lean_dec_ref(v___x_6478_);
return v_res_6487_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6491_; lean_object* v___x_6492_; 
v___x_6491_ = l_Lake_Hash_nil;
v___x_6492_ = lean_box_uint64(v___x_6491_);
return v___x_6492_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6493_, lean_object* v___f_6494_, lean_object* v_extraDepTrace_6495_, lean_object* v_weakArgs_6496_, lean_object* v_oFile_6497_, lean_object* v_compiler_6498_, lean_object* v___x_6499_, lean_object* v___f_6500_, lean_object* v_srcFile_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_){
_start:
{
lean_object* v_log_6509_; uint8_t v_action_6510_; uint8_t v_wantsRebuild_6511_; lean_object* v_trace_6512_; lean_object* v_buildTime_6513_; lean_object* v___x_6515_; uint8_t v_isShared_6516_; uint8_t v_isSharedCheck_6598_; 
v_log_6509_ = lean_ctor_get(v___y_6507_, 0);
v_action_6510_ = lean_ctor_get_uint8(v___y_6507_, sizeof(void*)*3);
v_wantsRebuild_6511_ = lean_ctor_get_uint8(v___y_6507_, sizeof(void*)*3 + 1);
v_trace_6512_ = lean_ctor_get(v___y_6507_, 1);
v_buildTime_6513_ = lean_ctor_get(v___y_6507_, 2);
v_isSharedCheck_6598_ = !lean_is_exclusive(v___y_6507_);
if (v_isSharedCheck_6598_ == 0)
{
v___x_6515_ = v___y_6507_;
v_isShared_6516_ = v_isSharedCheck_6598_;
goto v_resetjp_6514_;
}
else
{
lean_inc(v_buildTime_6513_);
lean_inc(v_trace_6512_);
lean_inc(v_log_6509_);
lean_dec(v___y_6507_);
v___x_6515_ = lean_box(0);
v_isShared_6516_ = v_isSharedCheck_6598_;
goto v_resetjp_6514_;
}
v_resetjp_6514_:
{
lean_object* v___x_6517_; lean_object* v___x_6518_; uint64_t v___y_6520_; uint64_t v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; uint8_t v___x_6586_; 
v___x_6517_ = l_Lake_platformTrace;
v___x_6518_ = l_Lake_BuildTrace_mix(v_trace_6512_, v___x_6517_);
v___x_6583_ = l_Lake_Hash_nil;
v___x_6584_ = lean_unsigned_to_nat(0u);
v___x_6585_ = lean_array_get_size(v_traceArgs_6493_);
v___x_6586_ = lean_nat_dec_lt(v___x_6584_, v___x_6585_);
if (v___x_6586_ == 0)
{
lean_dec_ref(v___f_6500_);
lean_dec_ref(v___x_6499_);
v___y_6520_ = v___x_6583_;
goto v___jp_6519_;
}
else
{
uint8_t v___x_6587_; 
v___x_6587_ = lean_nat_dec_le(v___x_6585_, v___x_6585_);
if (v___x_6587_ == 0)
{
if (v___x_6586_ == 0)
{
lean_dec_ref(v___f_6500_);
lean_dec_ref(v___x_6499_);
v___y_6520_ = v___x_6583_;
goto v___jp_6519_;
}
else
{
size_t v___x_6588_; size_t v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; uint64_t v___x_6592_; 
v___x_6588_ = ((size_t)0ULL);
v___x_6589_ = lean_usize_of_nat(v___x_6585_);
v___x_6590_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6493_);
v___x_6591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6499_, v___f_6500_, v_traceArgs_6493_, v___x_6588_, v___x_6589_, v___x_6590_);
v___x_6592_ = lean_unbox_uint64(v___x_6591_);
lean_dec(v___x_6591_);
v___y_6520_ = v___x_6592_;
goto v___jp_6519_;
}
}
else
{
size_t v___x_6593_; size_t v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; uint64_t v___x_6597_; 
v___x_6593_ = ((size_t)0ULL);
v___x_6594_ = lean_usize_of_nat(v___x_6585_);
v___x_6595_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6493_);
v___x_6596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6499_, v___f_6500_, v_traceArgs_6493_, v___x_6593_, v___x_6594_, v___x_6595_);
v___x_6597_ = lean_unbox_uint64(v___x_6596_);
lean_dec(v___x_6596_);
v___y_6520_ = v___x_6597_;
goto v___jp_6519_;
}
}
v___jp_6519_:
{
lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6532_; 
v___x_6521_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6522_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6493_);
v___x_6523_ = lean_array_to_list(v_traceArgs_6493_);
v___x_6524_ = l_List_toString___redArg(v___f_6494_, v___x_6523_);
v___x_6525_ = lean_string_append(v___x_6522_, v___x_6524_);
lean_dec_ref(v___x_6524_);
v___x_6526_ = lean_string_append(v___x_6521_, v___x_6525_);
lean_dec_ref(v___x_6525_);
v___x_6527_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6528_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6529_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6529_, 0, v___x_6526_);
lean_ctor_set(v___x_6529_, 1, v___x_6527_);
lean_ctor_set(v___x_6529_, 2, v___x_6528_);
lean_ctor_set_uint64(v___x_6529_, sizeof(void*)*3, v___y_6520_);
v___x_6530_ = l_Lake_BuildTrace_mix(v___x_6518_, v___x_6529_);
if (v_isShared_6516_ == 0)
{
lean_ctor_set(v___x_6515_, 1, v___x_6530_);
v___x_6532_ = v___x_6515_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_log_6509_);
lean_ctor_set(v_reuseFailAlloc_6582_, 1, v___x_6530_);
lean_ctor_set(v_reuseFailAlloc_6582_, 2, v_buildTime_6513_);
lean_ctor_set_uint8(v_reuseFailAlloc_6582_, sizeof(void*)*3, v_action_6510_);
lean_ctor_set_uint8(v_reuseFailAlloc_6582_, sizeof(void*)*3 + 1, v_wantsRebuild_6511_);
v___x_6532_ = v_reuseFailAlloc_6582_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
lean_object* v___x_6533_; 
lean_inc_ref(v___y_6506_);
lean_inc(v___y_6505_);
lean_inc(v___y_6504_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
v___x_6533_ = lean_apply_7(v_extraDepTrace_6495_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___x_6532_, lean_box(0));
if (lean_obj_tag(v___x_6533_) == 0)
{
lean_object* v_a_6534_; lean_object* v_a_6535_; lean_object* v_log_6536_; uint8_t v_action_6537_; uint8_t v_wantsRebuild_6538_; lean_object* v_trace_6539_; lean_object* v_buildTime_6540_; lean_object* v___x_6542_; uint8_t v_isShared_6543_; uint8_t v_isSharedCheck_6572_; 
v_a_6534_ = lean_ctor_get(v___x_6533_, 1);
lean_inc(v_a_6534_);
v_a_6535_ = lean_ctor_get(v___x_6533_, 0);
lean_inc(v_a_6535_);
lean_dec_ref_known(v___x_6533_, 2);
v_log_6536_ = lean_ctor_get(v_a_6534_, 0);
v_action_6537_ = lean_ctor_get_uint8(v_a_6534_, sizeof(void*)*3);
v_wantsRebuild_6538_ = lean_ctor_get_uint8(v_a_6534_, sizeof(void*)*3 + 1);
v_trace_6539_ = lean_ctor_get(v_a_6534_, 1);
v_buildTime_6540_ = lean_ctor_get(v_a_6534_, 2);
v_isSharedCheck_6572_ = !lean_is_exclusive(v_a_6534_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6542_ = v_a_6534_;
v_isShared_6543_ = v_isSharedCheck_6572_;
goto v_resetjp_6541_;
}
else
{
lean_inc(v_buildTime_6540_);
lean_inc(v_trace_6539_);
lean_inc(v_log_6536_);
lean_dec(v_a_6534_);
v___x_6542_ = lean_box(0);
v_isShared_6543_ = v_isSharedCheck_6572_;
goto v_resetjp_6541_;
}
v_resetjp_6541_:
{
lean_object* v___x_6544_; lean_object* v___x_6546_; 
v___x_6544_ = l_Lake_BuildTrace_mix(v_trace_6539_, v_a_6535_);
if (v_isShared_6543_ == 0)
{
lean_ctor_set(v___x_6542_, 1, v___x_6544_);
v___x_6546_ = v___x_6542_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_log_6536_);
lean_ctor_set(v_reuseFailAlloc_6571_, 1, v___x_6544_);
lean_ctor_set(v_reuseFailAlloc_6571_, 2, v_buildTime_6540_);
lean_ctor_set_uint8(v_reuseFailAlloc_6571_, sizeof(void*)*3, v_action_6537_);
lean_ctor_set_uint8(v_reuseFailAlloc_6571_, sizeof(void*)*3 + 1, v_wantsRebuild_6538_);
v___x_6546_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
lean_object* v___x_6547_; lean_object* v___f_6548_; uint8_t v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; 
v___x_6547_ = l_Array_append___redArg(v_weakArgs_6496_, v_traceArgs_6493_);
lean_dec_ref(v_traceArgs_6493_);
lean_inc_ref(v_oFile_6497_);
v___f_6548_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6548_, 0, v_oFile_6497_);
lean_closure_set(v___f_6548_, 1, v_srcFile_6501_);
lean_closure_set(v___f_6548_, 2, v___x_6547_);
lean_closure_set(v___f_6548_, 3, v_compiler_6498_);
v___x_6549_ = 0;
v___x_6550_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6551_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6497_, v___f_6548_, v___x_6549_, v___x_6550_, v___x_6549_, v___x_6549_, v___x_6549_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___x_6546_);
if (lean_obj_tag(v___x_6551_) == 0)
{
lean_object* v_a_6552_; lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6561_; 
v_a_6552_ = lean_ctor_get(v___x_6551_, 0);
v_a_6553_ = lean_ctor_get(v___x_6551_, 1);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___x_6551_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6555_ = v___x_6551_;
v_isShared_6556_ = v_isSharedCheck_6561_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_inc(v_a_6552_);
lean_dec(v___x_6551_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6561_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v_path_6557_; lean_object* v___x_6559_; 
v_path_6557_ = lean_ctor_get(v_a_6552_, 1);
lean_inc_ref(v_path_6557_);
lean_dec(v_a_6552_);
if (v_isShared_6556_ == 0)
{
lean_ctor_set(v___x_6555_, 0, v_path_6557_);
v___x_6559_ = v___x_6555_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_path_6557_);
lean_ctor_set(v_reuseFailAlloc_6560_, 1, v_a_6553_);
v___x_6559_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
return v___x_6559_;
}
}
}
else
{
lean_object* v_a_6562_; lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6570_; 
v_a_6562_ = lean_ctor_get(v___x_6551_, 0);
v_a_6563_ = lean_ctor_get(v___x_6551_, 1);
v_isSharedCheck_6570_ = !lean_is_exclusive(v___x_6551_);
if (v_isSharedCheck_6570_ == 0)
{
v___x_6565_ = v___x_6551_;
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_inc(v_a_6562_);
lean_dec(v___x_6551_);
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
else
{
lean_object* v_a_6573_; lean_object* v_a_6574_; lean_object* v___x_6576_; uint8_t v_isShared_6577_; uint8_t v_isSharedCheck_6581_; 
lean_dec_ref(v___y_6502_);
lean_dec_ref(v_srcFile_6501_);
lean_dec_ref(v_compiler_6498_);
lean_dec_ref(v_oFile_6497_);
lean_dec_ref(v_weakArgs_6496_);
lean_dec_ref(v_traceArgs_6493_);
v_a_6573_ = lean_ctor_get(v___x_6533_, 0);
v_a_6574_ = lean_ctor_get(v___x_6533_, 1);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6533_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6576_ = v___x_6533_;
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
else
{
lean_inc(v_a_6574_);
lean_inc(v_a_6573_);
lean_dec(v___x_6533_);
v___x_6576_ = lean_box(0);
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
v_resetjp_6575_:
{
lean_object* v___x_6579_; 
if (v_isShared_6577_ == 0)
{
v___x_6579_ = v___x_6576_;
goto v_reusejp_6578_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6573_);
lean_ctor_set(v_reuseFailAlloc_6580_, 1, v_a_6574_);
v___x_6579_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6578_;
}
v_reusejp_6578_:
{
return v___x_6579_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6599_, lean_object* v___f_6600_, lean_object* v_extraDepTrace_6601_, lean_object* v_weakArgs_6602_, lean_object* v_oFile_6603_, lean_object* v_compiler_6604_, lean_object* v___x_6605_, lean_object* v___f_6606_, lean_object* v_srcFile_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l_Lake_buildO___lam__2(v_traceArgs_6599_, v___f_6600_, v_extraDepTrace_6601_, v_weakArgs_6602_, v_oFile_6603_, v_compiler_6604_, v___x_6605_, v___f_6606_, v_srcFile_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_);
lean_dec_ref(v___y_6612_);
lean_dec(v___y_6611_);
lean_dec(v___y_6610_);
lean_dec(v___y_6609_);
return v_res_6615_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6618_, lean_object* v_srcJob_6619_, lean_object* v_weakArgs_6620_, lean_object* v_traceArgs_6621_, lean_object* v_compiler_6622_, lean_object* v_extraDepTrace_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_, lean_object* v_a_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_){
_start:
{
lean_object* v___f_6631_; lean_object* v___x_6632_; lean_object* v___f_6633_; lean_object* v___x_6634_; lean_object* v___f_6635_; lean_object* v___x_6636_; uint8_t v___x_6637_; lean_object* v___x_6638_; 
v___f_6631_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6632_ = l_Lake_instDataKindFilePath;
v___f_6633_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6634_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6635_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6635_, 0, v_traceArgs_6621_);
lean_closure_set(v___f_6635_, 1, v___f_6633_);
lean_closure_set(v___f_6635_, 2, v_extraDepTrace_6623_);
lean_closure_set(v___f_6635_, 3, v_weakArgs_6620_);
lean_closure_set(v___f_6635_, 4, v_oFile_6618_);
lean_closure_set(v___f_6635_, 5, v_compiler_6622_);
lean_closure_set(v___f_6635_, 6, v___x_6634_);
lean_closure_set(v___f_6635_, 7, v___f_6631_);
v___x_6636_ = lean_unsigned_to_nat(0u);
v___x_6637_ = 0;
v___x_6638_ = l_Lake_Job_mapM___redArg(v___x_6632_, v_srcJob_6619_, v___f_6635_, v___x_6636_, v___x_6637_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_, v_a_6628_, v_a_6629_);
return v___x_6638_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6639_, lean_object* v_srcJob_6640_, lean_object* v_weakArgs_6641_, lean_object* v_traceArgs_6642_, lean_object* v_compiler_6643_, lean_object* v_extraDepTrace_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_){
_start:
{
lean_object* v_res_6652_; 
v_res_6652_ = l_Lake_buildO(v_oFile_6639_, v_srcJob_6640_, v_weakArgs_6641_, v_traceArgs_6642_, v_compiler_6643_, v_extraDepTrace_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_);
lean_dec_ref(v_a_6650_);
lean_dec_ref(v_a_6649_);
lean_dec(v_a_6648_);
lean_dec(v_a_6647_);
lean_dec(v_a_6646_);
return v_res_6652_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; 
v___x_6654_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6655_ = lean_unsigned_to_nat(2u);
v___x_6656_ = lean_mk_empty_array_with_capacity(v___x_6655_);
v___x_6657_ = lean_array_push(v___x_6656_, v___x_6654_);
return v___x_6657_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6658_, lean_object* v_traceArgs_6659_, lean_object* v_oFile_6660_, lean_object* v_srcFile_6661_, lean_object* v_leanIncludeDir_x3f_6662_, lean_object* v___y_6663_, lean_object* v___y_6664_, lean_object* v___y_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_){
_start:
{
lean_object* v_toContext_6670_; lean_object* v_lakeEnv_6671_; lean_object* v_log_6672_; uint8_t v_action_6673_; uint8_t v_wantsRebuild_6674_; lean_object* v_trace_6675_; lean_object* v_buildTime_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6717_; 
v_toContext_6670_ = lean_ctor_get(v___y_6667_, 1);
v_lakeEnv_6671_ = lean_ctor_get(v_toContext_6670_, 0);
v_log_6672_ = lean_ctor_get(v___y_6668_, 0);
v_action_6673_ = lean_ctor_get_uint8(v___y_6668_, sizeof(void*)*3);
v_wantsRebuild_6674_ = lean_ctor_get_uint8(v___y_6668_, sizeof(void*)*3 + 1);
v_trace_6675_ = lean_ctor_get(v___y_6668_, 1);
v_buildTime_6676_ = lean_ctor_get(v___y_6668_, 2);
v_isSharedCheck_6717_ = !lean_is_exclusive(v___y_6668_);
if (v_isSharedCheck_6717_ == 0)
{
v___x_6678_ = v___y_6668_;
v_isShared_6679_ = v_isSharedCheck_6717_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_buildTime_6676_);
lean_inc(v_trace_6675_);
lean_inc(v_log_6672_);
lean_dec(v___y_6668_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6717_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v_lean_6680_; lean_object* v___y_6682_; 
v_lean_6680_ = lean_ctor_get(v_lakeEnv_6671_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6662_) == 0)
{
lean_object* v_includeDir_6715_; 
v_includeDir_6715_ = lean_ctor_get(v_lean_6680_, 4);
lean_inc_ref(v_includeDir_6715_);
v___y_6682_ = v_includeDir_6715_;
goto v___jp_6681_;
}
else
{
lean_object* v_val_6716_; 
v_val_6716_ = lean_ctor_get(v_leanIncludeDir_x3f_6662_, 0);
lean_inc(v_val_6716_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6662_, 1);
v___y_6682_ = v_val_6716_;
goto v___jp_6681_;
}
v___jp_6681_:
{
lean_object* v_cc_6683_; lean_object* v_ccFlags_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v_cc_6683_ = lean_ctor_get(v_lean_6680_, 14);
v_ccFlags_6684_ = lean_ctor_get(v_lean_6680_, 18);
v___x_6685_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6686_ = lean_array_push(v___x_6685_, v___y_6682_);
v___x_6687_ = l_Array_append___redArg(v___x_6686_, v_ccFlags_6684_);
v___x_6688_ = l_Array_append___redArg(v___x_6687_, v_weakArgs_6658_);
v___x_6689_ = l_Array_append___redArg(v___x_6688_, v_traceArgs_6659_);
lean_inc_ref(v_cc_6683_);
v___x_6690_ = l_Lake_compileO(v_oFile_6660_, v_srcFile_6661_, v___x_6689_, v_cc_6683_, v_log_6672_);
lean_dec_ref(v___x_6689_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v_a_6691_; lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6702_; 
v_a_6691_ = lean_ctor_get(v___x_6690_, 0);
v_a_6692_ = lean_ctor_get(v___x_6690_, 1);
v_isSharedCheck_6702_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6702_ == 0)
{
v___x_6694_ = v___x_6690_;
v_isShared_6695_ = v_isSharedCheck_6702_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_inc(v_a_6691_);
lean_dec(v___x_6690_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6702_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v___x_6697_; 
if (v_isShared_6679_ == 0)
{
lean_ctor_set(v___x_6678_, 0, v_a_6692_);
v___x_6697_ = v___x_6678_;
goto v_reusejp_6696_;
}
else
{
lean_object* v_reuseFailAlloc_6701_; 
v_reuseFailAlloc_6701_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_a_6692_);
lean_ctor_set(v_reuseFailAlloc_6701_, 1, v_trace_6675_);
lean_ctor_set(v_reuseFailAlloc_6701_, 2, v_buildTime_6676_);
lean_ctor_set_uint8(v_reuseFailAlloc_6701_, sizeof(void*)*3, v_action_6673_);
lean_ctor_set_uint8(v_reuseFailAlloc_6701_, sizeof(void*)*3 + 1, v_wantsRebuild_6674_);
v___x_6697_ = v_reuseFailAlloc_6701_;
goto v_reusejp_6696_;
}
v_reusejp_6696_:
{
lean_object* v___x_6699_; 
if (v_isShared_6695_ == 0)
{
lean_ctor_set(v___x_6694_, 1, v___x_6697_);
v___x_6699_ = v___x_6694_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6700_; 
v_reuseFailAlloc_6700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_a_6691_);
lean_ctor_set(v_reuseFailAlloc_6700_, 1, v___x_6697_);
v___x_6699_ = v_reuseFailAlloc_6700_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
return v___x_6699_;
}
}
}
}
else
{
lean_object* v_a_6703_; lean_object* v_a_6704_; lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6714_; 
v_a_6703_ = lean_ctor_get(v___x_6690_, 0);
v_a_6704_ = lean_ctor_get(v___x_6690_, 1);
v_isSharedCheck_6714_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6714_ == 0)
{
v___x_6706_ = v___x_6690_;
v_isShared_6707_ = v_isSharedCheck_6714_;
goto v_resetjp_6705_;
}
else
{
lean_inc(v_a_6704_);
lean_inc(v_a_6703_);
lean_dec(v___x_6690_);
v___x_6706_ = lean_box(0);
v_isShared_6707_ = v_isSharedCheck_6714_;
goto v_resetjp_6705_;
}
v_resetjp_6705_:
{
lean_object* v___x_6709_; 
if (v_isShared_6679_ == 0)
{
lean_ctor_set(v___x_6678_, 0, v_a_6704_);
v___x_6709_ = v___x_6678_;
goto v_reusejp_6708_;
}
else
{
lean_object* v_reuseFailAlloc_6713_; 
v_reuseFailAlloc_6713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6713_, 0, v_a_6704_);
lean_ctor_set(v_reuseFailAlloc_6713_, 1, v_trace_6675_);
lean_ctor_set(v_reuseFailAlloc_6713_, 2, v_buildTime_6676_);
lean_ctor_set_uint8(v_reuseFailAlloc_6713_, sizeof(void*)*3, v_action_6673_);
lean_ctor_set_uint8(v_reuseFailAlloc_6713_, sizeof(void*)*3 + 1, v_wantsRebuild_6674_);
v___x_6709_ = v_reuseFailAlloc_6713_;
goto v_reusejp_6708_;
}
v_reusejp_6708_:
{
lean_object* v___x_6711_; 
if (v_isShared_6707_ == 0)
{
lean_ctor_set(v___x_6706_, 1, v___x_6709_);
v___x_6711_ = v___x_6706_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6703_);
lean_ctor_set(v_reuseFailAlloc_6712_, 1, v___x_6709_);
v___x_6711_ = v_reuseFailAlloc_6712_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
return v___x_6711_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6718_, lean_object* v_traceArgs_6719_, lean_object* v_oFile_6720_, lean_object* v_srcFile_6721_, lean_object* v_leanIncludeDir_x3f_6722_, lean_object* v___y_6723_, lean_object* v___y_6724_, lean_object* v___y_6725_, lean_object* v___y_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_){
_start:
{
lean_object* v_res_6730_; 
v_res_6730_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6718_, v_traceArgs_6719_, v_oFile_6720_, v_srcFile_6721_, v_leanIncludeDir_x3f_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
lean_dec_ref(v___y_6727_);
lean_dec(v___y_6726_);
lean_dec(v___y_6725_);
lean_dec(v___y_6724_);
lean_dec_ref(v___y_6723_);
lean_dec_ref(v_traceArgs_6719_);
lean_dec_ref(v_weakArgs_6718_);
return v_res_6730_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6731_, size_t v_i_6732_, size_t v_stop_6733_, uint64_t v_b_6734_){
_start:
{
uint8_t v___x_6735_; 
v___x_6735_ = lean_usize_dec_eq(v_i_6732_, v_stop_6733_);
if (v___x_6735_ == 0)
{
lean_object* v___x_6736_; uint64_t v___x_6737_; uint64_t v___x_6738_; uint64_t v___x_6739_; uint64_t v___x_6740_; size_t v___x_6741_; size_t v___x_6742_; 
v___x_6736_ = lean_array_uget_borrowed(v_as_6731_, v_i_6732_);
v___x_6737_ = l_Lake_Hash_nil;
v___x_6738_ = lean_string_hash(v___x_6736_);
v___x_6739_ = lean_uint64_mix_hash(v___x_6737_, v___x_6738_);
v___x_6740_ = lean_uint64_mix_hash(v_b_6734_, v___x_6739_);
v___x_6741_ = ((size_t)1ULL);
v___x_6742_ = lean_usize_add(v_i_6732_, v___x_6741_);
v_i_6732_ = v___x_6742_;
v_b_6734_ = v___x_6740_;
goto _start;
}
else
{
return v_b_6734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6744_, lean_object* v_i_6745_, lean_object* v_stop_6746_, lean_object* v_b_6747_){
_start:
{
size_t v_i_boxed_6748_; size_t v_stop_boxed_6749_; uint64_t v_b_boxed_6750_; uint64_t v_res_6751_; lean_object* v_r_6752_; 
v_i_boxed_6748_ = lean_unbox_usize(v_i_6745_);
lean_dec(v_i_6745_);
v_stop_boxed_6749_ = lean_unbox_usize(v_stop_6746_);
lean_dec(v_stop_6746_);
v_b_boxed_6750_ = lean_unbox_uint64(v_b_6747_);
lean_dec_ref(v_b_6747_);
v_res_6751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6744_, v_i_boxed_6748_, v_stop_boxed_6749_, v_b_boxed_6750_);
lean_dec_ref(v_as_6744_);
v_r_6752_ = lean_box_uint64(v_res_6751_);
return v_r_6752_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6754_, lean_object* v_x_6755_){
_start:
{
if (lean_obj_tag(v_x_6755_) == 0)
{
return v_x_6754_;
}
else
{
lean_object* v_head_6756_; lean_object* v_tail_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; 
v_head_6756_ = lean_ctor_get(v_x_6755_, 0);
v_tail_6757_ = lean_ctor_get(v_x_6755_, 1);
v___x_6758_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6759_ = lean_string_append(v_x_6754_, v___x_6758_);
v___x_6760_ = lean_string_append(v___x_6759_, v_head_6756_);
v_x_6754_ = v___x_6760_;
v_x_6755_ = v_tail_6757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6762_, lean_object* v_x_6763_){
_start:
{
lean_object* v_res_6764_; 
v_res_6764_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6762_, v_x_6763_);
lean_dec(v_x_6763_);
return v_res_6764_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6768_){
_start:
{
if (lean_obj_tag(v_x_6768_) == 0)
{
lean_object* v___x_6769_; 
v___x_6769_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6769_;
}
else
{
lean_object* v_tail_6770_; 
v_tail_6770_ = lean_ctor_get(v_x_6768_, 1);
if (lean_obj_tag(v_tail_6770_) == 0)
{
lean_object* v_head_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; 
v_head_6771_ = lean_ctor_get(v_x_6768_, 0);
v___x_6772_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6773_ = lean_string_append(v___x_6772_, v_head_6771_);
v___x_6774_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6775_ = lean_string_append(v___x_6773_, v___x_6774_);
return v___x_6775_;
}
else
{
lean_object* v_head_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; uint32_t v___x_6780_; lean_object* v___x_6781_; 
v_head_6776_ = lean_ctor_get(v_x_6768_, 0);
v___x_6777_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6778_ = lean_string_append(v___x_6777_, v_head_6776_);
v___x_6779_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6778_, v_tail_6770_);
v___x_6780_ = 93;
v___x_6781_ = lean_string_push(v___x_6779_, v___x_6780_);
return v___x_6781_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6782_){
_start:
{
lean_object* v_res_6783_; 
v_res_6783_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6782_);
lean_dec(v_x_6782_);
return v_res_6783_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6784_, lean_object* v_traceArgs_6785_, lean_object* v_oFile_6786_, lean_object* v_leanIncludeDir_x3f_6787_, lean_object* v_srcFile_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_){
_start:
{
lean_object* v_log_6796_; uint8_t v_action_6797_; uint8_t v_wantsRebuild_6798_; lean_object* v_trace_6799_; lean_object* v_buildTime_6800_; lean_object* v___x_6802_; uint8_t v_isShared_6803_; uint8_t v_isSharedCheck_6857_; 
v_log_6796_ = lean_ctor_get(v___y_6794_, 0);
v_action_6797_ = lean_ctor_get_uint8(v___y_6794_, sizeof(void*)*3);
v_wantsRebuild_6798_ = lean_ctor_get_uint8(v___y_6794_, sizeof(void*)*3 + 1);
v_trace_6799_ = lean_ctor_get(v___y_6794_, 1);
v_buildTime_6800_ = lean_ctor_get(v___y_6794_, 2);
v_isSharedCheck_6857_ = !lean_is_exclusive(v___y_6794_);
if (v_isSharedCheck_6857_ == 0)
{
v___x_6802_ = v___y_6794_;
v_isShared_6803_ = v_isSharedCheck_6857_;
goto v_resetjp_6801_;
}
else
{
lean_inc(v_buildTime_6800_);
lean_inc(v_trace_6799_);
lean_inc(v_log_6796_);
lean_dec(v___y_6794_);
v___x_6802_ = lean_box(0);
v_isShared_6803_ = v_isSharedCheck_6857_;
goto v_resetjp_6801_;
}
v_resetjp_6801_:
{
lean_object* v_leanTrace_6804_; lean_object* v___f_6805_; lean_object* v___x_6806_; uint64_t v___y_6808_; uint64_t v___x_6846_; lean_object* v___x_6847_; lean_object* v___x_6848_; uint8_t v___x_6849_; 
v_leanTrace_6804_ = lean_ctor_get(v___y_6793_, 2);
lean_inc_ref(v_oFile_6786_);
lean_inc_ref(v_traceArgs_6785_);
v___f_6805_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6805_, 0, v_weakArgs_6784_);
lean_closure_set(v___f_6805_, 1, v_traceArgs_6785_);
lean_closure_set(v___f_6805_, 2, v_oFile_6786_);
lean_closure_set(v___f_6805_, 3, v_srcFile_6788_);
lean_closure_set(v___f_6805_, 4, v_leanIncludeDir_x3f_6787_);
lean_inc_ref(v_leanTrace_6804_);
v___x_6806_ = l_Lake_BuildTrace_mix(v_trace_6799_, v_leanTrace_6804_);
v___x_6846_ = l_Lake_Hash_nil;
v___x_6847_ = lean_unsigned_to_nat(0u);
v___x_6848_ = lean_array_get_size(v_traceArgs_6785_);
v___x_6849_ = lean_nat_dec_lt(v___x_6847_, v___x_6848_);
if (v___x_6849_ == 0)
{
v___y_6808_ = v___x_6846_;
goto v___jp_6807_;
}
else
{
uint8_t v___x_6850_; 
v___x_6850_ = lean_nat_dec_le(v___x_6848_, v___x_6848_);
if (v___x_6850_ == 0)
{
if (v___x_6849_ == 0)
{
v___y_6808_ = v___x_6846_;
goto v___jp_6807_;
}
else
{
size_t v___x_6851_; size_t v___x_6852_; uint64_t v___x_6853_; 
v___x_6851_ = ((size_t)0ULL);
v___x_6852_ = lean_usize_of_nat(v___x_6848_);
v___x_6853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6785_, v___x_6851_, v___x_6852_, v___x_6846_);
v___y_6808_ = v___x_6853_;
goto v___jp_6807_;
}
}
else
{
size_t v___x_6854_; size_t v___x_6855_; uint64_t v___x_6856_; 
v___x_6854_ = ((size_t)0ULL);
v___x_6855_ = lean_usize_of_nat(v___x_6848_);
v___x_6856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6785_, v___x_6854_, v___x_6855_, v___x_6846_);
v___y_6808_ = v___x_6856_;
goto v___jp_6807_;
}
}
v___jp_6807_:
{
lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6822_; 
v___x_6809_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6810_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6811_ = lean_array_to_list(v_traceArgs_6785_);
v___x_6812_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6811_);
lean_dec(v___x_6811_);
v___x_6813_ = lean_string_append(v___x_6810_, v___x_6812_);
lean_dec_ref(v___x_6812_);
v___x_6814_ = lean_string_append(v___x_6809_, v___x_6813_);
lean_dec_ref(v___x_6813_);
v___x_6815_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6816_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6817_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6817_, 0, v___x_6814_);
lean_ctor_set(v___x_6817_, 1, v___x_6815_);
lean_ctor_set(v___x_6817_, 2, v___x_6816_);
lean_ctor_set_uint64(v___x_6817_, sizeof(void*)*3, v___y_6808_);
v___x_6818_ = l_Lake_BuildTrace_mix(v___x_6806_, v___x_6817_);
v___x_6819_ = l_Lake_platformTrace;
v___x_6820_ = l_Lake_BuildTrace_mix(v___x_6818_, v___x_6819_);
if (v_isShared_6803_ == 0)
{
lean_ctor_set(v___x_6802_, 1, v___x_6820_);
v___x_6822_ = v___x_6802_;
goto v_reusejp_6821_;
}
else
{
lean_object* v_reuseFailAlloc_6845_; 
v_reuseFailAlloc_6845_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6845_, 0, v_log_6796_);
lean_ctor_set(v_reuseFailAlloc_6845_, 1, v___x_6820_);
lean_ctor_set(v_reuseFailAlloc_6845_, 2, v_buildTime_6800_);
lean_ctor_set_uint8(v_reuseFailAlloc_6845_, sizeof(void*)*3, v_action_6797_);
lean_ctor_set_uint8(v_reuseFailAlloc_6845_, sizeof(void*)*3 + 1, v_wantsRebuild_6798_);
v___x_6822_ = v_reuseFailAlloc_6845_;
goto v_reusejp_6821_;
}
v_reusejp_6821_:
{
uint8_t v___x_6823_; lean_object* v___x_6824_; lean_object* v___x_6825_; 
v___x_6823_ = 0;
v___x_6824_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6825_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6786_, v___f_6805_, v___x_6823_, v___x_6824_, v___x_6823_, v___x_6823_, v___x_6823_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___x_6822_);
if (lean_obj_tag(v___x_6825_) == 0)
{
lean_object* v_a_6826_; lean_object* v_a_6827_; lean_object* v___x_6829_; uint8_t v_isShared_6830_; uint8_t v_isSharedCheck_6835_; 
v_a_6826_ = lean_ctor_get(v___x_6825_, 0);
v_a_6827_ = lean_ctor_get(v___x_6825_, 1);
v_isSharedCheck_6835_ = !lean_is_exclusive(v___x_6825_);
if (v_isSharedCheck_6835_ == 0)
{
v___x_6829_ = v___x_6825_;
v_isShared_6830_ = v_isSharedCheck_6835_;
goto v_resetjp_6828_;
}
else
{
lean_inc(v_a_6827_);
lean_inc(v_a_6826_);
lean_dec(v___x_6825_);
v___x_6829_ = lean_box(0);
v_isShared_6830_ = v_isSharedCheck_6835_;
goto v_resetjp_6828_;
}
v_resetjp_6828_:
{
lean_object* v_path_6831_; lean_object* v___x_6833_; 
v_path_6831_ = lean_ctor_get(v_a_6826_, 1);
lean_inc_ref(v_path_6831_);
lean_dec(v_a_6826_);
if (v_isShared_6830_ == 0)
{
lean_ctor_set(v___x_6829_, 0, v_path_6831_);
v___x_6833_ = v___x_6829_;
goto v_reusejp_6832_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v_path_6831_);
lean_ctor_set(v_reuseFailAlloc_6834_, 1, v_a_6827_);
v___x_6833_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6832_;
}
v_reusejp_6832_:
{
return v___x_6833_;
}
}
}
else
{
lean_object* v_a_6836_; lean_object* v_a_6837_; lean_object* v___x_6839_; uint8_t v_isShared_6840_; uint8_t v_isSharedCheck_6844_; 
v_a_6836_ = lean_ctor_get(v___x_6825_, 0);
v_a_6837_ = lean_ctor_get(v___x_6825_, 1);
v_isSharedCheck_6844_ = !lean_is_exclusive(v___x_6825_);
if (v_isSharedCheck_6844_ == 0)
{
v___x_6839_ = v___x_6825_;
v_isShared_6840_ = v_isSharedCheck_6844_;
goto v_resetjp_6838_;
}
else
{
lean_inc(v_a_6837_);
lean_inc(v_a_6836_);
lean_dec(v___x_6825_);
v___x_6839_ = lean_box(0);
v_isShared_6840_ = v_isSharedCheck_6844_;
goto v_resetjp_6838_;
}
v_resetjp_6838_:
{
lean_object* v___x_6842_; 
if (v_isShared_6840_ == 0)
{
v___x_6842_ = v___x_6839_;
goto v_reusejp_6841_;
}
else
{
lean_object* v_reuseFailAlloc_6843_; 
v_reuseFailAlloc_6843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6836_);
lean_ctor_set(v_reuseFailAlloc_6843_, 1, v_a_6837_);
v___x_6842_ = v_reuseFailAlloc_6843_;
goto v_reusejp_6841_;
}
v_reusejp_6841_:
{
return v___x_6842_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6858_, lean_object* v_traceArgs_6859_, lean_object* v_oFile_6860_, lean_object* v_leanIncludeDir_x3f_6861_, lean_object* v_srcFile_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_){
_start:
{
lean_object* v_res_6870_; 
v_res_6870_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6858_, v_traceArgs_6859_, v_oFile_6860_, v_leanIncludeDir_x3f_6861_, v_srcFile_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_);
lean_dec_ref(v___y_6867_);
lean_dec(v___y_6866_);
lean_dec(v___y_6865_);
lean_dec(v___y_6864_);
return v_res_6870_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6871_, lean_object* v_srcJob_6872_, lean_object* v_weakArgs_6873_, lean_object* v_traceArgs_6874_, lean_object* v_leanIncludeDir_x3f_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_, lean_object* v_a_6881_){
_start:
{
lean_object* v___f_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; uint8_t v___x_6886_; lean_object* v___x_6887_; 
v___f_6883_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6883_, 0, v_weakArgs_6873_);
lean_closure_set(v___f_6883_, 1, v_traceArgs_6874_);
lean_closure_set(v___f_6883_, 2, v_oFile_6871_);
lean_closure_set(v___f_6883_, 3, v_leanIncludeDir_x3f_6875_);
v___x_6884_ = l_Lake_instDataKindFilePath;
v___x_6885_ = lean_unsigned_to_nat(0u);
v___x_6886_ = 0;
v___x_6887_ = l_Lake_Job_mapM___redArg(v___x_6884_, v_srcJob_6872_, v___f_6883_, v___x_6885_, v___x_6886_, v_a_6876_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_, v_a_6881_);
return v___x_6887_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6888_, lean_object* v_srcJob_6889_, lean_object* v_weakArgs_6890_, lean_object* v_traceArgs_6891_, lean_object* v_leanIncludeDir_x3f_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_){
_start:
{
lean_object* v_res_6900_; 
v_res_6900_ = l_Lake_buildLeanO(v_oFile_6888_, v_srcJob_6889_, v_weakArgs_6890_, v_traceArgs_6891_, v_leanIncludeDir_x3f_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_, v_a_6898_);
lean_dec_ref(v_a_6898_);
lean_dec_ref(v_a_6897_);
lean_dec(v_a_6896_);
lean_dec(v_a_6895_);
lean_dec(v_a_6894_);
return v_res_6900_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6901_, lean_object* v_oFiles_6902_, uint8_t v_thin_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_, lean_object* v___y_6907_, lean_object* v___y_6908_, lean_object* v___y_6909_){
_start:
{
lean_object* v_toContext_6911_; lean_object* v_lakeEnv_6912_; lean_object* v_lean_6913_; lean_object* v_log_6914_; uint8_t v_action_6915_; uint8_t v_wantsRebuild_6916_; lean_object* v_trace_6917_; lean_object* v_buildTime_6918_; lean_object* v___x_6920_; uint8_t v_isShared_6921_; uint8_t v_isSharedCheck_6948_; 
v_toContext_6911_ = lean_ctor_get(v___y_6908_, 1);
v_lakeEnv_6912_ = lean_ctor_get(v_toContext_6911_, 0);
v_lean_6913_ = lean_ctor_get(v_lakeEnv_6912_, 1);
v_log_6914_ = lean_ctor_get(v___y_6909_, 0);
v_action_6915_ = lean_ctor_get_uint8(v___y_6909_, sizeof(void*)*3);
v_wantsRebuild_6916_ = lean_ctor_get_uint8(v___y_6909_, sizeof(void*)*3 + 1);
v_trace_6917_ = lean_ctor_get(v___y_6909_, 1);
v_buildTime_6918_ = lean_ctor_get(v___y_6909_, 2);
v_isSharedCheck_6948_ = !lean_is_exclusive(v___y_6909_);
if (v_isSharedCheck_6948_ == 0)
{
v___x_6920_ = v___y_6909_;
v_isShared_6921_ = v_isSharedCheck_6948_;
goto v_resetjp_6919_;
}
else
{
lean_inc(v_buildTime_6918_);
lean_inc(v_trace_6917_);
lean_inc(v_log_6914_);
lean_dec(v___y_6909_);
v___x_6920_ = lean_box(0);
v_isShared_6921_ = v_isSharedCheck_6948_;
goto v_resetjp_6919_;
}
v_resetjp_6919_:
{
lean_object* v_ar_6922_; lean_object* v___x_6923_; 
v_ar_6922_ = lean_ctor_get(v_lean_6913_, 13);
lean_inc_ref(v_ar_6922_);
v___x_6923_ = l_Lake_compileStaticLib(v_libFile_6901_, v_oFiles_6902_, v_ar_6922_, v_thin_6903_, v_log_6914_);
if (lean_obj_tag(v___x_6923_) == 0)
{
lean_object* v_a_6924_; lean_object* v_a_6925_; lean_object* v___x_6927_; uint8_t v_isShared_6928_; uint8_t v_isSharedCheck_6935_; 
v_a_6924_ = lean_ctor_get(v___x_6923_, 0);
v_a_6925_ = lean_ctor_get(v___x_6923_, 1);
v_isSharedCheck_6935_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6935_ == 0)
{
v___x_6927_ = v___x_6923_;
v_isShared_6928_ = v_isSharedCheck_6935_;
goto v_resetjp_6926_;
}
else
{
lean_inc(v_a_6925_);
lean_inc(v_a_6924_);
lean_dec(v___x_6923_);
v___x_6927_ = lean_box(0);
v_isShared_6928_ = v_isSharedCheck_6935_;
goto v_resetjp_6926_;
}
v_resetjp_6926_:
{
lean_object* v___x_6930_; 
if (v_isShared_6921_ == 0)
{
lean_ctor_set(v___x_6920_, 0, v_a_6925_);
v___x_6930_ = v___x_6920_;
goto v_reusejp_6929_;
}
else
{
lean_object* v_reuseFailAlloc_6934_; 
v_reuseFailAlloc_6934_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6934_, 0, v_a_6925_);
lean_ctor_set(v_reuseFailAlloc_6934_, 1, v_trace_6917_);
lean_ctor_set(v_reuseFailAlloc_6934_, 2, v_buildTime_6918_);
lean_ctor_set_uint8(v_reuseFailAlloc_6934_, sizeof(void*)*3, v_action_6915_);
lean_ctor_set_uint8(v_reuseFailAlloc_6934_, sizeof(void*)*3 + 1, v_wantsRebuild_6916_);
v___x_6930_ = v_reuseFailAlloc_6934_;
goto v_reusejp_6929_;
}
v_reusejp_6929_:
{
lean_object* v___x_6932_; 
if (v_isShared_6928_ == 0)
{
lean_ctor_set(v___x_6927_, 1, v___x_6930_);
v___x_6932_ = v___x_6927_;
goto v_reusejp_6931_;
}
else
{
lean_object* v_reuseFailAlloc_6933_; 
v_reuseFailAlloc_6933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6924_);
lean_ctor_set(v_reuseFailAlloc_6933_, 1, v___x_6930_);
v___x_6932_ = v_reuseFailAlloc_6933_;
goto v_reusejp_6931_;
}
v_reusejp_6931_:
{
return v___x_6932_;
}
}
}
}
else
{
lean_object* v_a_6936_; lean_object* v_a_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6947_; 
v_a_6936_ = lean_ctor_get(v___x_6923_, 0);
v_a_6937_ = lean_ctor_get(v___x_6923_, 1);
v_isSharedCheck_6947_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6947_ == 0)
{
v___x_6939_ = v___x_6923_;
v_isShared_6940_ = v_isSharedCheck_6947_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_a_6937_);
lean_inc(v_a_6936_);
lean_dec(v___x_6923_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6947_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
lean_object* v___x_6942_; 
if (v_isShared_6921_ == 0)
{
lean_ctor_set(v___x_6920_, 0, v_a_6937_);
v___x_6942_ = v___x_6920_;
goto v_reusejp_6941_;
}
else
{
lean_object* v_reuseFailAlloc_6946_; 
v_reuseFailAlloc_6946_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6946_, 0, v_a_6937_);
lean_ctor_set(v_reuseFailAlloc_6946_, 1, v_trace_6917_);
lean_ctor_set(v_reuseFailAlloc_6946_, 2, v_buildTime_6918_);
lean_ctor_set_uint8(v_reuseFailAlloc_6946_, sizeof(void*)*3, v_action_6915_);
lean_ctor_set_uint8(v_reuseFailAlloc_6946_, sizeof(void*)*3 + 1, v_wantsRebuild_6916_);
v___x_6942_ = v_reuseFailAlloc_6946_;
goto v_reusejp_6941_;
}
v_reusejp_6941_:
{
lean_object* v___x_6944_; 
if (v_isShared_6940_ == 0)
{
lean_ctor_set(v___x_6939_, 1, v___x_6942_);
v___x_6944_ = v___x_6939_;
goto v_reusejp_6943_;
}
else
{
lean_object* v_reuseFailAlloc_6945_; 
v_reuseFailAlloc_6945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6945_, 0, v_a_6936_);
lean_ctor_set(v_reuseFailAlloc_6945_, 1, v___x_6942_);
v___x_6944_ = v_reuseFailAlloc_6945_;
goto v_reusejp_6943_;
}
v_reusejp_6943_:
{
return v___x_6944_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6949_, lean_object* v_oFiles_6950_, lean_object* v_thin_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_){
_start:
{
uint8_t v_thin_boxed_6959_; lean_object* v_res_6960_; 
v_thin_boxed_6959_ = lean_unbox(v_thin_6951_);
v_res_6960_ = l_Lake_buildStaticLib___lam__0(v_libFile_6949_, v_oFiles_6950_, v_thin_boxed_6959_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_, v___y_6956_, v___y_6957_);
lean_dec_ref(v___y_6956_);
lean_dec(v___y_6955_);
lean_dec(v___y_6954_);
lean_dec(v___y_6953_);
lean_dec_ref(v___y_6952_);
return v_res_6960_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6962_, uint8_t v_thin_6963_, lean_object* v_oFiles_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_){
_start:
{
lean_object* v___x_6972_; lean_object* v___f_6973_; uint8_t v___x_6974_; lean_object* v___x_6975_; uint8_t v___x_6976_; lean_object* v___x_6977_; 
v___x_6972_ = lean_box(v_thin_6963_);
lean_inc_ref(v_libFile_6962_);
v___f_6973_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6973_, 0, v_libFile_6962_);
lean_closure_set(v___f_6973_, 1, v_oFiles_6964_);
lean_closure_set(v___f_6973_, 2, v___x_6972_);
v___x_6974_ = 0;
v___x_6975_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6976_ = 1;
v___x_6977_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6962_, v___f_6973_, v___x_6974_, v___x_6975_, v___x_6976_, v___x_6974_, v___x_6974_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
if (lean_obj_tag(v___x_6977_) == 0)
{
lean_object* v_a_6978_; lean_object* v_a_6979_; lean_object* v___x_6981_; uint8_t v_isShared_6982_; uint8_t v_isSharedCheck_6987_; 
v_a_6978_ = lean_ctor_get(v___x_6977_, 0);
v_a_6979_ = lean_ctor_get(v___x_6977_, 1);
v_isSharedCheck_6987_ = !lean_is_exclusive(v___x_6977_);
if (v_isSharedCheck_6987_ == 0)
{
v___x_6981_ = v___x_6977_;
v_isShared_6982_ = v_isSharedCheck_6987_;
goto v_resetjp_6980_;
}
else
{
lean_inc(v_a_6979_);
lean_inc(v_a_6978_);
lean_dec(v___x_6977_);
v___x_6981_ = lean_box(0);
v_isShared_6982_ = v_isSharedCheck_6987_;
goto v_resetjp_6980_;
}
v_resetjp_6980_:
{
lean_object* v_path_6983_; lean_object* v___x_6985_; 
v_path_6983_ = lean_ctor_get(v_a_6978_, 1);
lean_inc_ref(v_path_6983_);
lean_dec(v_a_6978_);
if (v_isShared_6982_ == 0)
{
lean_ctor_set(v___x_6981_, 0, v_path_6983_);
v___x_6985_ = v___x_6981_;
goto v_reusejp_6984_;
}
else
{
lean_object* v_reuseFailAlloc_6986_; 
v_reuseFailAlloc_6986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6986_, 0, v_path_6983_);
lean_ctor_set(v_reuseFailAlloc_6986_, 1, v_a_6979_);
v___x_6985_ = v_reuseFailAlloc_6986_;
goto v_reusejp_6984_;
}
v_reusejp_6984_:
{
return v___x_6985_;
}
}
}
else
{
lean_object* v_a_6988_; lean_object* v_a_6989_; lean_object* v___x_6991_; uint8_t v_isShared_6992_; uint8_t v_isSharedCheck_6996_; 
v_a_6988_ = lean_ctor_get(v___x_6977_, 0);
v_a_6989_ = lean_ctor_get(v___x_6977_, 1);
v_isSharedCheck_6996_ = !lean_is_exclusive(v___x_6977_);
if (v_isSharedCheck_6996_ == 0)
{
v___x_6991_ = v___x_6977_;
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
else
{
lean_inc(v_a_6989_);
lean_inc(v_a_6988_);
lean_dec(v___x_6977_);
v___x_6991_ = lean_box(0);
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
v_resetjp_6990_:
{
lean_object* v___x_6994_; 
if (v_isShared_6992_ == 0)
{
v___x_6994_ = v___x_6991_;
goto v_reusejp_6993_;
}
else
{
lean_object* v_reuseFailAlloc_6995_; 
v_reuseFailAlloc_6995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6988_);
lean_ctor_set(v_reuseFailAlloc_6995_, 1, v_a_6989_);
v___x_6994_ = v_reuseFailAlloc_6995_;
goto v_reusejp_6993_;
}
v_reusejp_6993_:
{
return v___x_6994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6997_, lean_object* v_thin_6998_, lean_object* v_oFiles_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_){
_start:
{
uint8_t v_thin_boxed_7007_; lean_object* v_res_7008_; 
v_thin_boxed_7007_ = lean_unbox(v_thin_6998_);
v_res_7008_ = l_Lake_buildStaticLib___lam__1(v_libFile_6997_, v_thin_boxed_7007_, v_oFiles_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_);
lean_dec_ref(v___y_7004_);
lean_dec(v___y_7003_);
lean_dec(v___y_7002_);
lean_dec(v___y_7001_);
return v_res_7008_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_7010_, lean_object* v_oFileJobs_7011_, uint8_t v_thin_7012_, lean_object* v_a_7013_, lean_object* v_a_7014_, lean_object* v_a_7015_, lean_object* v_a_7016_, lean_object* v_a_7017_, lean_object* v_a_7018_){
_start:
{
lean_object* v___x_7020_; lean_object* v___f_7021_; lean_object* v___x_7022_; lean_object* v___x_7023_; lean_object* v___x_7024_; lean_object* v___x_7025_; uint8_t v___x_7026_; lean_object* v___x_7027_; 
v___x_7020_ = lean_box(v_thin_7012_);
v___f_7021_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_7021_, 0, v_libFile_7010_);
lean_closure_set(v___f_7021_, 1, v___x_7020_);
v___x_7022_ = l_Lake_instDataKindFilePath;
v___x_7023_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_7024_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_7011_, v___x_7023_);
v___x_7025_ = lean_unsigned_to_nat(0u);
v___x_7026_ = 0;
v___x_7027_ = l_Lake_Job_mapM___redArg(v___x_7022_, v___x_7024_, v___f_7021_, v___x_7025_, v___x_7026_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_, v_a_7018_);
return v___x_7027_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_7028_, lean_object* v_oFileJobs_7029_, lean_object* v_thin_7030_, lean_object* v_a_7031_, lean_object* v_a_7032_, lean_object* v_a_7033_, lean_object* v_a_7034_, lean_object* v_a_7035_, lean_object* v_a_7036_, lean_object* v_a_7037_){
_start:
{
uint8_t v_thin_boxed_7038_; lean_object* v_res_7039_; 
v_thin_boxed_7038_ = lean_unbox(v_thin_7030_);
v_res_7039_ = l_Lake_buildStaticLib(v_libFile_7028_, v_oFileJobs_7029_, v_thin_boxed_7038_, v_a_7031_, v_a_7032_, v_a_7033_, v_a_7034_, v_a_7035_, v_a_7036_);
lean_dec_ref(v_a_7036_);
lean_dec_ref(v_a_7035_);
lean_dec(v_a_7034_);
lean_dec(v_a_7033_);
lean_dec(v_a_7032_);
lean_dec_ref(v_oFileJobs_7029_);
return v_res_7039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7040_, size_t v_sz_7041_, size_t v_i_7042_, lean_object* v_b_7043_){
_start:
{
uint8_t v___x_7044_; 
v___x_7044_ = lean_usize_dec_lt(v_i_7042_, v_sz_7041_);
if (v___x_7044_ == 0)
{
return v_b_7043_;
}
else
{
lean_object* v_a_7045_; lean_object* v___x_7046_; size_t v___x_7047_; size_t v___x_7048_; 
v_a_7045_ = lean_array_uget_borrowed(v_as_7040_, v_i_7042_);
lean_inc(v_a_7045_);
v___x_7046_ = lean_array_push(v_b_7043_, v_a_7045_);
v___x_7047_ = ((size_t)1ULL);
v___x_7048_ = lean_usize_add(v_i_7042_, v___x_7047_);
v_i_7042_ = v___x_7048_;
v_b_7043_ = v___x_7046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7050_, lean_object* v_sz_7051_, lean_object* v_i_7052_, lean_object* v_b_7053_){
_start:
{
size_t v_sz_boxed_7054_; size_t v_i_boxed_7055_; lean_object* v_res_7056_; 
v_sz_boxed_7054_ = lean_unbox_usize(v_sz_7051_);
lean_dec(v_sz_7051_);
v_i_boxed_7055_ = lean_unbox_usize(v_i_7052_);
lean_dec(v_i_7052_);
v_res_7056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7050_, v_sz_boxed_7054_, v_i_boxed_7055_, v_b_7053_);
lean_dec_ref(v_as_7050_);
return v_res_7056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7059_, size_t v_sz_7060_, size_t v_i_7061_, lean_object* v_b_7062_){
_start:
{
uint8_t v___x_7063_; 
v___x_7063_ = lean_usize_dec_lt(v_i_7061_, v_sz_7060_);
if (v___x_7063_ == 0)
{
return v_b_7062_;
}
else
{
lean_object* v_a_7064_; lean_object* v_args_7066_; lean_object* v___x_7074_; 
v_a_7064_ = lean_array_uget_borrowed(v_as_7059_, v_i_7061_);
lean_inc(v_a_7064_);
v___x_7074_ = l_Lake_Dynlib_dir_x3f(v_a_7064_);
if (lean_obj_tag(v___x_7074_) == 1)
{
lean_object* v_val_7075_; lean_object* v___x_7076_; lean_object* v___x_7077_; lean_object* v___x_7078_; 
v_val_7075_ = lean_ctor_get(v___x_7074_, 0);
lean_inc(v_val_7075_);
lean_dec_ref_known(v___x_7074_, 1);
v___x_7076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7077_ = lean_string_append(v___x_7076_, v_val_7075_);
lean_dec(v_val_7075_);
v___x_7078_ = lean_array_push(v_b_7062_, v___x_7077_);
v_args_7066_ = v___x_7078_;
goto v___jp_7065_;
}
else
{
lean_dec(v___x_7074_);
v_args_7066_ = v_b_7062_;
goto v___jp_7065_;
}
v___jp_7065_:
{
lean_object* v_name_7067_; lean_object* v___x_7068_; lean_object* v___x_7069_; lean_object* v___x_7070_; size_t v___x_7071_; size_t v___x_7072_; 
v_name_7067_ = lean_ctor_get(v_a_7064_, 1);
v___x_7068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7069_ = lean_string_append(v___x_7068_, v_name_7067_);
v___x_7070_ = lean_array_push(v_args_7066_, v___x_7069_);
v___x_7071_ = ((size_t)1ULL);
v___x_7072_ = lean_usize_add(v_i_7061_, v___x_7071_);
v_i_7061_ = v___x_7072_;
v_b_7062_ = v___x_7070_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7079_, lean_object* v_sz_7080_, lean_object* v_i_7081_, lean_object* v_b_7082_){
_start:
{
size_t v_sz_boxed_7083_; size_t v_i_boxed_7084_; lean_object* v_res_7085_; 
v_sz_boxed_7083_ = lean_unbox_usize(v_sz_7080_);
lean_dec(v_sz_7080_);
v_i_boxed_7084_ = lean_unbox_usize(v_i_7081_);
lean_dec(v_i_7081_);
v_res_7085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7079_, v_sz_boxed_7083_, v_i_boxed_7084_, v_b_7082_);
lean_dec_ref(v_as_7079_);
return v_res_7085_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7086_, lean_object* v_libs_7087_){
_start:
{
lean_object* v_args_7088_; size_t v_sz_7089_; size_t v___x_7090_; lean_object* v___x_7091_; size_t v_sz_7092_; lean_object* v___x_7093_; 
v_args_7088_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7089_ = lean_array_size(v_objs_7086_);
v___x_7090_ = ((size_t)0ULL);
v___x_7091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7086_, v_sz_7089_, v___x_7090_, v_args_7088_);
v_sz_7092_ = lean_array_size(v_libs_7087_);
v___x_7093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7087_, v_sz_7092_, v___x_7090_, v___x_7091_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7094_, lean_object* v_libs_7095_){
_start:
{
lean_object* v_res_7096_; 
v_res_7096_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7094_, v_libs_7095_);
lean_dec_ref(v_libs_7095_);
lean_dec_ref(v_objs_7094_);
return v_res_7096_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7097_, lean_object* v_t_7098_){
_start:
{
if (lean_obj_tag(v_t_7098_) == 0)
{
lean_object* v_k_7099_; lean_object* v_l_7100_; lean_object* v_r_7101_; uint8_t v___x_7102_; 
v_k_7099_ = lean_ctor_get(v_t_7098_, 1);
v_l_7100_ = lean_ctor_get(v_t_7098_, 3);
v_r_7101_ = lean_ctor_get(v_t_7098_, 4);
v___x_7102_ = lean_string_compare(v_k_7097_, v_k_7099_);
switch(v___x_7102_)
{
case 0:
{
v_t_7098_ = v_l_7100_;
goto _start;
}
case 1:
{
uint8_t v___x_7104_; 
v___x_7104_ = 1;
return v___x_7104_;
}
default: 
{
v_t_7098_ = v_r_7101_;
goto _start;
}
}
}
else
{
uint8_t v___x_7106_; 
v___x_7106_ = 0;
return v___x_7106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7107_, lean_object* v_t_7108_){
_start:
{
uint8_t v_res_7109_; lean_object* v_r_7110_; 
v_res_7109_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7107_, v_t_7108_);
lean_dec(v_t_7108_);
lean_dec_ref(v_k_7107_);
v_r_7110_ = lean_box(v_res_7109_);
return v_r_7110_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7111_, lean_object* v_x_7112_){
_start:
{
if (lean_obj_tag(v_x_7112_) == 0)
{
uint8_t v___x_7113_; 
v___x_7113_ = 0;
return v___x_7113_;
}
else
{
lean_object* v_head_7114_; lean_object* v_tail_7115_; uint8_t v___x_7116_; 
v_head_7114_ = lean_ctor_get(v_x_7112_, 0);
v_tail_7115_ = lean_ctor_get(v_x_7112_, 1);
v___x_7116_ = lean_string_dec_eq(v_a_7111_, v_head_7114_);
if (v___x_7116_ == 0)
{
v_x_7112_ = v_tail_7115_;
goto _start;
}
else
{
return v___x_7116_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7118_, lean_object* v_x_7119_){
_start:
{
uint8_t v_res_7120_; lean_object* v_r_7121_; 
v_res_7120_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7118_, v_x_7119_);
lean_dec(v_x_7119_);
lean_dec_ref(v_a_7118_);
v_r_7121_ = lean_box(v_res_7120_);
return v_r_7121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7122_, lean_object* v_v_7123_, lean_object* v_t_7124_){
_start:
{
if (lean_obj_tag(v_t_7124_) == 0)
{
lean_object* v_size_7125_; lean_object* v_k_7126_; lean_object* v_v_7127_; lean_object* v_l_7128_; lean_object* v_r_7129_; lean_object* v___x_7131_; uint8_t v_isShared_7132_; uint8_t v_isSharedCheck_7409_; 
v_size_7125_ = lean_ctor_get(v_t_7124_, 0);
v_k_7126_ = lean_ctor_get(v_t_7124_, 1);
v_v_7127_ = lean_ctor_get(v_t_7124_, 2);
v_l_7128_ = lean_ctor_get(v_t_7124_, 3);
v_r_7129_ = lean_ctor_get(v_t_7124_, 4);
v_isSharedCheck_7409_ = !lean_is_exclusive(v_t_7124_);
if (v_isSharedCheck_7409_ == 0)
{
v___x_7131_ = v_t_7124_;
v_isShared_7132_ = v_isSharedCheck_7409_;
goto v_resetjp_7130_;
}
else
{
lean_inc(v_r_7129_);
lean_inc(v_l_7128_);
lean_inc(v_v_7127_);
lean_inc(v_k_7126_);
lean_inc(v_size_7125_);
lean_dec(v_t_7124_);
v___x_7131_ = lean_box(0);
v_isShared_7132_ = v_isSharedCheck_7409_;
goto v_resetjp_7130_;
}
v_resetjp_7130_:
{
uint8_t v___x_7133_; 
v___x_7133_ = lean_string_compare(v_k_7122_, v_k_7126_);
switch(v___x_7133_)
{
case 0:
{
lean_object* v_impl_7134_; lean_object* v___x_7135_; 
lean_dec(v_size_7125_);
v_impl_7134_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7122_, v_v_7123_, v_l_7128_);
v___x_7135_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7129_) == 0)
{
lean_object* v_size_7136_; lean_object* v_size_7137_; lean_object* v_k_7138_; lean_object* v_v_7139_; lean_object* v_l_7140_; lean_object* v_r_7141_; lean_object* v___x_7142_; lean_object* v___x_7143_; uint8_t v___x_7144_; 
v_size_7136_ = lean_ctor_get(v_r_7129_, 0);
v_size_7137_ = lean_ctor_get(v_impl_7134_, 0);
lean_inc(v_size_7137_);
v_k_7138_ = lean_ctor_get(v_impl_7134_, 1);
lean_inc(v_k_7138_);
v_v_7139_ = lean_ctor_get(v_impl_7134_, 2);
lean_inc(v_v_7139_);
v_l_7140_ = lean_ctor_get(v_impl_7134_, 3);
lean_inc(v_l_7140_);
v_r_7141_ = lean_ctor_get(v_impl_7134_, 4);
lean_inc(v_r_7141_);
v___x_7142_ = lean_unsigned_to_nat(3u);
v___x_7143_ = lean_nat_mul(v___x_7142_, v_size_7136_);
v___x_7144_ = lean_nat_dec_lt(v___x_7143_, v_size_7137_);
lean_dec(v___x_7143_);
if (v___x_7144_ == 0)
{
lean_object* v___x_7145_; lean_object* v___x_7146_; lean_object* v___x_7148_; 
lean_dec(v_r_7141_);
lean_dec(v_l_7140_);
lean_dec(v_v_7139_);
lean_dec(v_k_7138_);
v___x_7145_ = lean_nat_add(v___x_7135_, v_size_7137_);
lean_dec(v_size_7137_);
v___x_7146_ = lean_nat_add(v___x_7145_, v_size_7136_);
lean_dec(v___x_7145_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 3, v_impl_7134_);
lean_ctor_set(v___x_7131_, 0, v___x_7146_);
v___x_7148_ = v___x_7131_;
goto v_reusejp_7147_;
}
else
{
lean_object* v_reuseFailAlloc_7149_; 
v_reuseFailAlloc_7149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7149_, 0, v___x_7146_);
lean_ctor_set(v_reuseFailAlloc_7149_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7149_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7149_, 3, v_impl_7134_);
lean_ctor_set(v_reuseFailAlloc_7149_, 4, v_r_7129_);
v___x_7148_ = v_reuseFailAlloc_7149_;
goto v_reusejp_7147_;
}
v_reusejp_7147_:
{
return v___x_7148_;
}
}
else
{
lean_object* v___x_7151_; uint8_t v_isShared_7152_; uint8_t v_isSharedCheck_7215_; 
v_isSharedCheck_7215_ = !lean_is_exclusive(v_impl_7134_);
if (v_isSharedCheck_7215_ == 0)
{
lean_object* v_unused_7216_; lean_object* v_unused_7217_; lean_object* v_unused_7218_; lean_object* v_unused_7219_; lean_object* v_unused_7220_; 
v_unused_7216_ = lean_ctor_get(v_impl_7134_, 4);
lean_dec(v_unused_7216_);
v_unused_7217_ = lean_ctor_get(v_impl_7134_, 3);
lean_dec(v_unused_7217_);
v_unused_7218_ = lean_ctor_get(v_impl_7134_, 2);
lean_dec(v_unused_7218_);
v_unused_7219_ = lean_ctor_get(v_impl_7134_, 1);
lean_dec(v_unused_7219_);
v_unused_7220_ = lean_ctor_get(v_impl_7134_, 0);
lean_dec(v_unused_7220_);
v___x_7151_ = v_impl_7134_;
v_isShared_7152_ = v_isSharedCheck_7215_;
goto v_resetjp_7150_;
}
else
{
lean_dec(v_impl_7134_);
v___x_7151_ = lean_box(0);
v_isShared_7152_ = v_isSharedCheck_7215_;
goto v_resetjp_7150_;
}
v_resetjp_7150_:
{
lean_object* v_size_7153_; lean_object* v_size_7154_; lean_object* v_k_7155_; lean_object* v_v_7156_; lean_object* v_l_7157_; lean_object* v_r_7158_; lean_object* v___x_7159_; lean_object* v___x_7160_; uint8_t v___x_7161_; 
v_size_7153_ = lean_ctor_get(v_l_7140_, 0);
v_size_7154_ = lean_ctor_get(v_r_7141_, 0);
v_k_7155_ = lean_ctor_get(v_r_7141_, 1);
v_v_7156_ = lean_ctor_get(v_r_7141_, 2);
v_l_7157_ = lean_ctor_get(v_r_7141_, 3);
v_r_7158_ = lean_ctor_get(v_r_7141_, 4);
v___x_7159_ = lean_unsigned_to_nat(2u);
v___x_7160_ = lean_nat_mul(v___x_7159_, v_size_7153_);
v___x_7161_ = lean_nat_dec_lt(v_size_7154_, v___x_7160_);
lean_dec(v___x_7160_);
if (v___x_7161_ == 0)
{
lean_object* v___x_7163_; uint8_t v_isShared_7164_; uint8_t v_isSharedCheck_7190_; 
lean_inc(v_r_7158_);
lean_inc(v_l_7157_);
lean_inc(v_v_7156_);
lean_inc(v_k_7155_);
v_isSharedCheck_7190_ = !lean_is_exclusive(v_r_7141_);
if (v_isSharedCheck_7190_ == 0)
{
lean_object* v_unused_7191_; lean_object* v_unused_7192_; lean_object* v_unused_7193_; lean_object* v_unused_7194_; lean_object* v_unused_7195_; 
v_unused_7191_ = lean_ctor_get(v_r_7141_, 4);
lean_dec(v_unused_7191_);
v_unused_7192_ = lean_ctor_get(v_r_7141_, 3);
lean_dec(v_unused_7192_);
v_unused_7193_ = lean_ctor_get(v_r_7141_, 2);
lean_dec(v_unused_7193_);
v_unused_7194_ = lean_ctor_get(v_r_7141_, 1);
lean_dec(v_unused_7194_);
v_unused_7195_ = lean_ctor_get(v_r_7141_, 0);
lean_dec(v_unused_7195_);
v___x_7163_ = v_r_7141_;
v_isShared_7164_ = v_isSharedCheck_7190_;
goto v_resetjp_7162_;
}
else
{
lean_dec(v_r_7141_);
v___x_7163_ = lean_box(0);
v_isShared_7164_ = v_isSharedCheck_7190_;
goto v_resetjp_7162_;
}
v_resetjp_7162_:
{
lean_object* v___x_7165_; lean_object* v___x_7166_; lean_object* v___y_7168_; lean_object* v___y_7169_; lean_object* v___y_7170_; lean_object* v___x_7178_; lean_object* v___y_7180_; 
v___x_7165_ = lean_nat_add(v___x_7135_, v_size_7137_);
lean_dec(v_size_7137_);
v___x_7166_ = lean_nat_add(v___x_7165_, v_size_7136_);
lean_dec(v___x_7165_);
v___x_7178_ = lean_nat_add(v___x_7135_, v_size_7153_);
if (lean_obj_tag(v_l_7157_) == 0)
{
lean_object* v_size_7188_; 
v_size_7188_ = lean_ctor_get(v_l_7157_, 0);
lean_inc(v_size_7188_);
v___y_7180_ = v_size_7188_;
goto v___jp_7179_;
}
else
{
lean_object* v___x_7189_; 
v___x_7189_ = lean_unsigned_to_nat(0u);
v___y_7180_ = v___x_7189_;
goto v___jp_7179_;
}
v___jp_7167_:
{
lean_object* v___x_7171_; lean_object* v___x_7173_; 
v___x_7171_ = lean_nat_add(v___y_7168_, v___y_7170_);
lean_dec(v___y_7170_);
lean_dec(v___y_7168_);
if (v_isShared_7164_ == 0)
{
lean_ctor_set(v___x_7163_, 4, v_r_7129_);
lean_ctor_set(v___x_7163_, 3, v_r_7158_);
lean_ctor_set(v___x_7163_, 2, v_v_7127_);
lean_ctor_set(v___x_7163_, 1, v_k_7126_);
lean_ctor_set(v___x_7163_, 0, v___x_7171_);
v___x_7173_ = v___x_7163_;
goto v_reusejp_7172_;
}
else
{
lean_object* v_reuseFailAlloc_7177_; 
v_reuseFailAlloc_7177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7177_, 0, v___x_7171_);
lean_ctor_set(v_reuseFailAlloc_7177_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7177_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7177_, 3, v_r_7158_);
lean_ctor_set(v_reuseFailAlloc_7177_, 4, v_r_7129_);
v___x_7173_ = v_reuseFailAlloc_7177_;
goto v_reusejp_7172_;
}
v_reusejp_7172_:
{
lean_object* v___x_7175_; 
if (v_isShared_7152_ == 0)
{
lean_ctor_set(v___x_7151_, 4, v___x_7173_);
lean_ctor_set(v___x_7151_, 3, v___y_7169_);
lean_ctor_set(v___x_7151_, 2, v_v_7156_);
lean_ctor_set(v___x_7151_, 1, v_k_7155_);
lean_ctor_set(v___x_7151_, 0, v___x_7166_);
v___x_7175_ = v___x_7151_;
goto v_reusejp_7174_;
}
else
{
lean_object* v_reuseFailAlloc_7176_; 
v_reuseFailAlloc_7176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7176_, 0, v___x_7166_);
lean_ctor_set(v_reuseFailAlloc_7176_, 1, v_k_7155_);
lean_ctor_set(v_reuseFailAlloc_7176_, 2, v_v_7156_);
lean_ctor_set(v_reuseFailAlloc_7176_, 3, v___y_7169_);
lean_ctor_set(v_reuseFailAlloc_7176_, 4, v___x_7173_);
v___x_7175_ = v_reuseFailAlloc_7176_;
goto v_reusejp_7174_;
}
v_reusejp_7174_:
{
return v___x_7175_;
}
}
}
v___jp_7179_:
{
lean_object* v___x_7181_; lean_object* v___x_7183_; 
v___x_7181_ = lean_nat_add(v___x_7178_, v___y_7180_);
lean_dec(v___y_7180_);
lean_dec(v___x_7178_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_l_7157_);
lean_ctor_set(v___x_7131_, 3, v_l_7140_);
lean_ctor_set(v___x_7131_, 2, v_v_7139_);
lean_ctor_set(v___x_7131_, 1, v_k_7138_);
lean_ctor_set(v___x_7131_, 0, v___x_7181_);
v___x_7183_ = v___x_7131_;
goto v_reusejp_7182_;
}
else
{
lean_object* v_reuseFailAlloc_7187_; 
v_reuseFailAlloc_7187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7187_, 0, v___x_7181_);
lean_ctor_set(v_reuseFailAlloc_7187_, 1, v_k_7138_);
lean_ctor_set(v_reuseFailAlloc_7187_, 2, v_v_7139_);
lean_ctor_set(v_reuseFailAlloc_7187_, 3, v_l_7140_);
lean_ctor_set(v_reuseFailAlloc_7187_, 4, v_l_7157_);
v___x_7183_ = v_reuseFailAlloc_7187_;
goto v_reusejp_7182_;
}
v_reusejp_7182_:
{
lean_object* v___x_7184_; 
v___x_7184_ = lean_nat_add(v___x_7135_, v_size_7136_);
if (lean_obj_tag(v_r_7158_) == 0)
{
lean_object* v_size_7185_; 
v_size_7185_ = lean_ctor_get(v_r_7158_, 0);
lean_inc(v_size_7185_);
v___y_7168_ = v___x_7184_;
v___y_7169_ = v___x_7183_;
v___y_7170_ = v_size_7185_;
goto v___jp_7167_;
}
else
{
lean_object* v___x_7186_; 
v___x_7186_ = lean_unsigned_to_nat(0u);
v___y_7168_ = v___x_7184_;
v___y_7169_ = v___x_7183_;
v___y_7170_ = v___x_7186_;
goto v___jp_7167_;
}
}
}
}
}
else
{
lean_object* v___x_7196_; lean_object* v___x_7197_; lean_object* v___x_7198_; lean_object* v___x_7199_; lean_object* v___x_7201_; 
lean_del_object(v___x_7131_);
v___x_7196_ = lean_nat_add(v___x_7135_, v_size_7137_);
lean_dec(v_size_7137_);
v___x_7197_ = lean_nat_add(v___x_7196_, v_size_7136_);
lean_dec(v___x_7196_);
v___x_7198_ = lean_nat_add(v___x_7135_, v_size_7136_);
v___x_7199_ = lean_nat_add(v___x_7198_, v_size_7154_);
lean_dec(v___x_7198_);
lean_inc_ref(v_r_7129_);
if (v_isShared_7152_ == 0)
{
lean_ctor_set(v___x_7151_, 4, v_r_7129_);
lean_ctor_set(v___x_7151_, 3, v_r_7141_);
lean_ctor_set(v___x_7151_, 2, v_v_7127_);
lean_ctor_set(v___x_7151_, 1, v_k_7126_);
lean_ctor_set(v___x_7151_, 0, v___x_7199_);
v___x_7201_ = v___x_7151_;
goto v_reusejp_7200_;
}
else
{
lean_object* v_reuseFailAlloc_7214_; 
v_reuseFailAlloc_7214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7214_, 0, v___x_7199_);
lean_ctor_set(v_reuseFailAlloc_7214_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7214_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7214_, 3, v_r_7141_);
lean_ctor_set(v_reuseFailAlloc_7214_, 4, v_r_7129_);
v___x_7201_ = v_reuseFailAlloc_7214_;
goto v_reusejp_7200_;
}
v_reusejp_7200_:
{
lean_object* v___x_7203_; uint8_t v_isShared_7204_; uint8_t v_isSharedCheck_7208_; 
v_isSharedCheck_7208_ = !lean_is_exclusive(v_r_7129_);
if (v_isSharedCheck_7208_ == 0)
{
lean_object* v_unused_7209_; lean_object* v_unused_7210_; lean_object* v_unused_7211_; lean_object* v_unused_7212_; lean_object* v_unused_7213_; 
v_unused_7209_ = lean_ctor_get(v_r_7129_, 4);
lean_dec(v_unused_7209_);
v_unused_7210_ = lean_ctor_get(v_r_7129_, 3);
lean_dec(v_unused_7210_);
v_unused_7211_ = lean_ctor_get(v_r_7129_, 2);
lean_dec(v_unused_7211_);
v_unused_7212_ = lean_ctor_get(v_r_7129_, 1);
lean_dec(v_unused_7212_);
v_unused_7213_ = lean_ctor_get(v_r_7129_, 0);
lean_dec(v_unused_7213_);
v___x_7203_ = v_r_7129_;
v_isShared_7204_ = v_isSharedCheck_7208_;
goto v_resetjp_7202_;
}
else
{
lean_dec(v_r_7129_);
v___x_7203_ = lean_box(0);
v_isShared_7204_ = v_isSharedCheck_7208_;
goto v_resetjp_7202_;
}
v_resetjp_7202_:
{
lean_object* v___x_7206_; 
if (v_isShared_7204_ == 0)
{
lean_ctor_set(v___x_7203_, 4, v___x_7201_);
lean_ctor_set(v___x_7203_, 3, v_l_7140_);
lean_ctor_set(v___x_7203_, 2, v_v_7139_);
lean_ctor_set(v___x_7203_, 1, v_k_7138_);
lean_ctor_set(v___x_7203_, 0, v___x_7197_);
v___x_7206_ = v___x_7203_;
goto v_reusejp_7205_;
}
else
{
lean_object* v_reuseFailAlloc_7207_; 
v_reuseFailAlloc_7207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7207_, 0, v___x_7197_);
lean_ctor_set(v_reuseFailAlloc_7207_, 1, v_k_7138_);
lean_ctor_set(v_reuseFailAlloc_7207_, 2, v_v_7139_);
lean_ctor_set(v_reuseFailAlloc_7207_, 3, v_l_7140_);
lean_ctor_set(v_reuseFailAlloc_7207_, 4, v___x_7201_);
v___x_7206_ = v_reuseFailAlloc_7207_;
goto v_reusejp_7205_;
}
v_reusejp_7205_:
{
return v___x_7206_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7221_; 
v_l_7221_ = lean_ctor_get(v_impl_7134_, 3);
lean_inc(v_l_7221_);
if (lean_obj_tag(v_l_7221_) == 0)
{
lean_object* v_r_7222_; lean_object* v_k_7223_; lean_object* v_v_7224_; lean_object* v___x_7226_; uint8_t v_isShared_7227_; uint8_t v_isSharedCheck_7235_; 
v_r_7222_ = lean_ctor_get(v_impl_7134_, 4);
v_k_7223_ = lean_ctor_get(v_impl_7134_, 1);
v_v_7224_ = lean_ctor_get(v_impl_7134_, 2);
v_isSharedCheck_7235_ = !lean_is_exclusive(v_impl_7134_);
if (v_isSharedCheck_7235_ == 0)
{
lean_object* v_unused_7236_; lean_object* v_unused_7237_; 
v_unused_7236_ = lean_ctor_get(v_impl_7134_, 3);
lean_dec(v_unused_7236_);
v_unused_7237_ = lean_ctor_get(v_impl_7134_, 0);
lean_dec(v_unused_7237_);
v___x_7226_ = v_impl_7134_;
v_isShared_7227_ = v_isSharedCheck_7235_;
goto v_resetjp_7225_;
}
else
{
lean_inc(v_r_7222_);
lean_inc(v_v_7224_);
lean_inc(v_k_7223_);
lean_dec(v_impl_7134_);
v___x_7226_ = lean_box(0);
v_isShared_7227_ = v_isSharedCheck_7235_;
goto v_resetjp_7225_;
}
v_resetjp_7225_:
{
lean_object* v___x_7228_; lean_object* v___x_7230_; 
v___x_7228_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7222_);
if (v_isShared_7227_ == 0)
{
lean_ctor_set(v___x_7226_, 3, v_r_7222_);
lean_ctor_set(v___x_7226_, 2, v_v_7127_);
lean_ctor_set(v___x_7226_, 1, v_k_7126_);
lean_ctor_set(v___x_7226_, 0, v___x_7135_);
v___x_7230_ = v___x_7226_;
goto v_reusejp_7229_;
}
else
{
lean_object* v_reuseFailAlloc_7234_; 
v_reuseFailAlloc_7234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7234_, 0, v___x_7135_);
lean_ctor_set(v_reuseFailAlloc_7234_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7234_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7234_, 3, v_r_7222_);
lean_ctor_set(v_reuseFailAlloc_7234_, 4, v_r_7222_);
v___x_7230_ = v_reuseFailAlloc_7234_;
goto v_reusejp_7229_;
}
v_reusejp_7229_:
{
lean_object* v___x_7232_; 
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v___x_7230_);
lean_ctor_set(v___x_7131_, 3, v_l_7221_);
lean_ctor_set(v___x_7131_, 2, v_v_7224_);
lean_ctor_set(v___x_7131_, 1, v_k_7223_);
lean_ctor_set(v___x_7131_, 0, v___x_7228_);
v___x_7232_ = v___x_7131_;
goto v_reusejp_7231_;
}
else
{
lean_object* v_reuseFailAlloc_7233_; 
v_reuseFailAlloc_7233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7233_, 0, v___x_7228_);
lean_ctor_set(v_reuseFailAlloc_7233_, 1, v_k_7223_);
lean_ctor_set(v_reuseFailAlloc_7233_, 2, v_v_7224_);
lean_ctor_set(v_reuseFailAlloc_7233_, 3, v_l_7221_);
lean_ctor_set(v_reuseFailAlloc_7233_, 4, v___x_7230_);
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
else
{
lean_object* v_r_7238_; 
v_r_7238_ = lean_ctor_get(v_impl_7134_, 4);
lean_inc(v_r_7238_);
if (lean_obj_tag(v_r_7238_) == 0)
{
lean_object* v_k_7239_; lean_object* v_v_7240_; lean_object* v___x_7242_; uint8_t v_isShared_7243_; uint8_t v_isSharedCheck_7263_; 
v_k_7239_ = lean_ctor_get(v_impl_7134_, 1);
v_v_7240_ = lean_ctor_get(v_impl_7134_, 2);
v_isSharedCheck_7263_ = !lean_is_exclusive(v_impl_7134_);
if (v_isSharedCheck_7263_ == 0)
{
lean_object* v_unused_7264_; lean_object* v_unused_7265_; lean_object* v_unused_7266_; 
v_unused_7264_ = lean_ctor_get(v_impl_7134_, 4);
lean_dec(v_unused_7264_);
v_unused_7265_ = lean_ctor_get(v_impl_7134_, 3);
lean_dec(v_unused_7265_);
v_unused_7266_ = lean_ctor_get(v_impl_7134_, 0);
lean_dec(v_unused_7266_);
v___x_7242_ = v_impl_7134_;
v_isShared_7243_ = v_isSharedCheck_7263_;
goto v_resetjp_7241_;
}
else
{
lean_inc(v_v_7240_);
lean_inc(v_k_7239_);
lean_dec(v_impl_7134_);
v___x_7242_ = lean_box(0);
v_isShared_7243_ = v_isSharedCheck_7263_;
goto v_resetjp_7241_;
}
v_resetjp_7241_:
{
lean_object* v_k_7244_; lean_object* v_v_7245_; lean_object* v___x_7247_; uint8_t v_isShared_7248_; uint8_t v_isSharedCheck_7259_; 
v_k_7244_ = lean_ctor_get(v_r_7238_, 1);
v_v_7245_ = lean_ctor_get(v_r_7238_, 2);
v_isSharedCheck_7259_ = !lean_is_exclusive(v_r_7238_);
if (v_isSharedCheck_7259_ == 0)
{
lean_object* v_unused_7260_; lean_object* v_unused_7261_; lean_object* v_unused_7262_; 
v_unused_7260_ = lean_ctor_get(v_r_7238_, 4);
lean_dec(v_unused_7260_);
v_unused_7261_ = lean_ctor_get(v_r_7238_, 3);
lean_dec(v_unused_7261_);
v_unused_7262_ = lean_ctor_get(v_r_7238_, 0);
lean_dec(v_unused_7262_);
v___x_7247_ = v_r_7238_;
v_isShared_7248_ = v_isSharedCheck_7259_;
goto v_resetjp_7246_;
}
else
{
lean_inc(v_v_7245_);
lean_inc(v_k_7244_);
lean_dec(v_r_7238_);
v___x_7247_ = lean_box(0);
v_isShared_7248_ = v_isSharedCheck_7259_;
goto v_resetjp_7246_;
}
v_resetjp_7246_:
{
lean_object* v___x_7249_; lean_object* v___x_7251_; 
v___x_7249_ = lean_unsigned_to_nat(3u);
if (v_isShared_7248_ == 0)
{
lean_ctor_set(v___x_7247_, 4, v_l_7221_);
lean_ctor_set(v___x_7247_, 3, v_l_7221_);
lean_ctor_set(v___x_7247_, 2, v_v_7240_);
lean_ctor_set(v___x_7247_, 1, v_k_7239_);
lean_ctor_set(v___x_7247_, 0, v___x_7135_);
v___x_7251_ = v___x_7247_;
goto v_reusejp_7250_;
}
else
{
lean_object* v_reuseFailAlloc_7258_; 
v_reuseFailAlloc_7258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7258_, 0, v___x_7135_);
lean_ctor_set(v_reuseFailAlloc_7258_, 1, v_k_7239_);
lean_ctor_set(v_reuseFailAlloc_7258_, 2, v_v_7240_);
lean_ctor_set(v_reuseFailAlloc_7258_, 3, v_l_7221_);
lean_ctor_set(v_reuseFailAlloc_7258_, 4, v_l_7221_);
v___x_7251_ = v_reuseFailAlloc_7258_;
goto v_reusejp_7250_;
}
v_reusejp_7250_:
{
lean_object* v___x_7253_; 
if (v_isShared_7243_ == 0)
{
lean_ctor_set(v___x_7242_, 4, v_l_7221_);
lean_ctor_set(v___x_7242_, 2, v_v_7127_);
lean_ctor_set(v___x_7242_, 1, v_k_7126_);
lean_ctor_set(v___x_7242_, 0, v___x_7135_);
v___x_7253_ = v___x_7242_;
goto v_reusejp_7252_;
}
else
{
lean_object* v_reuseFailAlloc_7257_; 
v_reuseFailAlloc_7257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7257_, 0, v___x_7135_);
lean_ctor_set(v_reuseFailAlloc_7257_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7257_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7257_, 3, v_l_7221_);
lean_ctor_set(v_reuseFailAlloc_7257_, 4, v_l_7221_);
v___x_7253_ = v_reuseFailAlloc_7257_;
goto v_reusejp_7252_;
}
v_reusejp_7252_:
{
lean_object* v___x_7255_; 
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v___x_7253_);
lean_ctor_set(v___x_7131_, 3, v___x_7251_);
lean_ctor_set(v___x_7131_, 2, v_v_7245_);
lean_ctor_set(v___x_7131_, 1, v_k_7244_);
lean_ctor_set(v___x_7131_, 0, v___x_7249_);
v___x_7255_ = v___x_7131_;
goto v_reusejp_7254_;
}
else
{
lean_object* v_reuseFailAlloc_7256_; 
v_reuseFailAlloc_7256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7256_, 0, v___x_7249_);
lean_ctor_set(v_reuseFailAlloc_7256_, 1, v_k_7244_);
lean_ctor_set(v_reuseFailAlloc_7256_, 2, v_v_7245_);
lean_ctor_set(v_reuseFailAlloc_7256_, 3, v___x_7251_);
lean_ctor_set(v_reuseFailAlloc_7256_, 4, v___x_7253_);
v___x_7255_ = v_reuseFailAlloc_7256_;
goto v_reusejp_7254_;
}
v_reusejp_7254_:
{
return v___x_7255_;
}
}
}
}
}
}
else
{
lean_object* v___x_7267_; lean_object* v___x_7269_; 
v___x_7267_ = lean_unsigned_to_nat(2u);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_r_7238_);
lean_ctor_set(v___x_7131_, 3, v_impl_7134_);
lean_ctor_set(v___x_7131_, 0, v___x_7267_);
v___x_7269_ = v___x_7131_;
goto v_reusejp_7268_;
}
else
{
lean_object* v_reuseFailAlloc_7270_; 
v_reuseFailAlloc_7270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7270_, 0, v___x_7267_);
lean_ctor_set(v_reuseFailAlloc_7270_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7270_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7270_, 3, v_impl_7134_);
lean_ctor_set(v_reuseFailAlloc_7270_, 4, v_r_7238_);
v___x_7269_ = v_reuseFailAlloc_7270_;
goto v_reusejp_7268_;
}
v_reusejp_7268_:
{
return v___x_7269_;
}
}
}
}
}
case 1:
{
lean_object* v___x_7272_; 
lean_dec(v_v_7127_);
lean_dec(v_k_7126_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 2, v_v_7123_);
lean_ctor_set(v___x_7131_, 1, v_k_7122_);
v___x_7272_ = v___x_7131_;
goto v_reusejp_7271_;
}
else
{
lean_object* v_reuseFailAlloc_7273_; 
v_reuseFailAlloc_7273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7273_, 0, v_size_7125_);
lean_ctor_set(v_reuseFailAlloc_7273_, 1, v_k_7122_);
lean_ctor_set(v_reuseFailAlloc_7273_, 2, v_v_7123_);
lean_ctor_set(v_reuseFailAlloc_7273_, 3, v_l_7128_);
lean_ctor_set(v_reuseFailAlloc_7273_, 4, v_r_7129_);
v___x_7272_ = v_reuseFailAlloc_7273_;
goto v_reusejp_7271_;
}
v_reusejp_7271_:
{
return v___x_7272_;
}
}
default: 
{
lean_object* v_impl_7274_; lean_object* v___x_7275_; 
lean_dec(v_size_7125_);
v_impl_7274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7122_, v_v_7123_, v_r_7129_);
v___x_7275_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7128_) == 0)
{
lean_object* v_size_7276_; lean_object* v_size_7277_; lean_object* v_k_7278_; lean_object* v_v_7279_; lean_object* v_l_7280_; lean_object* v_r_7281_; lean_object* v___x_7282_; lean_object* v___x_7283_; uint8_t v___x_7284_; 
v_size_7276_ = lean_ctor_get(v_l_7128_, 0);
v_size_7277_ = lean_ctor_get(v_impl_7274_, 0);
lean_inc(v_size_7277_);
v_k_7278_ = lean_ctor_get(v_impl_7274_, 1);
lean_inc(v_k_7278_);
v_v_7279_ = lean_ctor_get(v_impl_7274_, 2);
lean_inc(v_v_7279_);
v_l_7280_ = lean_ctor_get(v_impl_7274_, 3);
lean_inc(v_l_7280_);
v_r_7281_ = lean_ctor_get(v_impl_7274_, 4);
lean_inc(v_r_7281_);
v___x_7282_ = lean_unsigned_to_nat(3u);
v___x_7283_ = lean_nat_mul(v___x_7282_, v_size_7276_);
v___x_7284_ = lean_nat_dec_lt(v___x_7283_, v_size_7277_);
lean_dec(v___x_7283_);
if (v___x_7284_ == 0)
{
lean_object* v___x_7285_; lean_object* v___x_7286_; lean_object* v___x_7288_; 
lean_dec(v_r_7281_);
lean_dec(v_l_7280_);
lean_dec(v_v_7279_);
lean_dec(v_k_7278_);
v___x_7285_ = lean_nat_add(v___x_7275_, v_size_7276_);
v___x_7286_ = lean_nat_add(v___x_7285_, v_size_7277_);
lean_dec(v_size_7277_);
lean_dec(v___x_7285_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_impl_7274_);
lean_ctor_set(v___x_7131_, 0, v___x_7286_);
v___x_7288_ = v___x_7131_;
goto v_reusejp_7287_;
}
else
{
lean_object* v_reuseFailAlloc_7289_; 
v_reuseFailAlloc_7289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7289_, 0, v___x_7286_);
lean_ctor_set(v_reuseFailAlloc_7289_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7289_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7289_, 3, v_l_7128_);
lean_ctor_set(v_reuseFailAlloc_7289_, 4, v_impl_7274_);
v___x_7288_ = v_reuseFailAlloc_7289_;
goto v_reusejp_7287_;
}
v_reusejp_7287_:
{
return v___x_7288_;
}
}
else
{
lean_object* v___x_7291_; uint8_t v_isShared_7292_; uint8_t v_isSharedCheck_7353_; 
v_isSharedCheck_7353_ = !lean_is_exclusive(v_impl_7274_);
if (v_isSharedCheck_7353_ == 0)
{
lean_object* v_unused_7354_; lean_object* v_unused_7355_; lean_object* v_unused_7356_; lean_object* v_unused_7357_; lean_object* v_unused_7358_; 
v_unused_7354_ = lean_ctor_get(v_impl_7274_, 4);
lean_dec(v_unused_7354_);
v_unused_7355_ = lean_ctor_get(v_impl_7274_, 3);
lean_dec(v_unused_7355_);
v_unused_7356_ = lean_ctor_get(v_impl_7274_, 2);
lean_dec(v_unused_7356_);
v_unused_7357_ = lean_ctor_get(v_impl_7274_, 1);
lean_dec(v_unused_7357_);
v_unused_7358_ = lean_ctor_get(v_impl_7274_, 0);
lean_dec(v_unused_7358_);
v___x_7291_ = v_impl_7274_;
v_isShared_7292_ = v_isSharedCheck_7353_;
goto v_resetjp_7290_;
}
else
{
lean_dec(v_impl_7274_);
v___x_7291_ = lean_box(0);
v_isShared_7292_ = v_isSharedCheck_7353_;
goto v_resetjp_7290_;
}
v_resetjp_7290_:
{
lean_object* v_size_7293_; lean_object* v_k_7294_; lean_object* v_v_7295_; lean_object* v_l_7296_; lean_object* v_r_7297_; lean_object* v_size_7298_; lean_object* v___x_7299_; lean_object* v___x_7300_; uint8_t v___x_7301_; 
v_size_7293_ = lean_ctor_get(v_l_7280_, 0);
v_k_7294_ = lean_ctor_get(v_l_7280_, 1);
v_v_7295_ = lean_ctor_get(v_l_7280_, 2);
v_l_7296_ = lean_ctor_get(v_l_7280_, 3);
v_r_7297_ = lean_ctor_get(v_l_7280_, 4);
v_size_7298_ = lean_ctor_get(v_r_7281_, 0);
v___x_7299_ = lean_unsigned_to_nat(2u);
v___x_7300_ = lean_nat_mul(v___x_7299_, v_size_7298_);
v___x_7301_ = lean_nat_dec_lt(v_size_7293_, v___x_7300_);
lean_dec(v___x_7300_);
if (v___x_7301_ == 0)
{
lean_object* v___x_7303_; uint8_t v_isShared_7304_; uint8_t v_isSharedCheck_7329_; 
lean_inc(v_r_7297_);
lean_inc(v_l_7296_);
lean_inc(v_v_7295_);
lean_inc(v_k_7294_);
v_isSharedCheck_7329_ = !lean_is_exclusive(v_l_7280_);
if (v_isSharedCheck_7329_ == 0)
{
lean_object* v_unused_7330_; lean_object* v_unused_7331_; lean_object* v_unused_7332_; lean_object* v_unused_7333_; lean_object* v_unused_7334_; 
v_unused_7330_ = lean_ctor_get(v_l_7280_, 4);
lean_dec(v_unused_7330_);
v_unused_7331_ = lean_ctor_get(v_l_7280_, 3);
lean_dec(v_unused_7331_);
v_unused_7332_ = lean_ctor_get(v_l_7280_, 2);
lean_dec(v_unused_7332_);
v_unused_7333_ = lean_ctor_get(v_l_7280_, 1);
lean_dec(v_unused_7333_);
v_unused_7334_ = lean_ctor_get(v_l_7280_, 0);
lean_dec(v_unused_7334_);
v___x_7303_ = v_l_7280_;
v_isShared_7304_ = v_isSharedCheck_7329_;
goto v_resetjp_7302_;
}
else
{
lean_dec(v_l_7280_);
v___x_7303_ = lean_box(0);
v_isShared_7304_ = v_isSharedCheck_7329_;
goto v_resetjp_7302_;
}
v_resetjp_7302_:
{
lean_object* v___x_7305_; lean_object* v___x_7306_; lean_object* v___y_7308_; lean_object* v___y_7309_; lean_object* v___y_7310_; lean_object* v___y_7319_; 
v___x_7305_ = lean_nat_add(v___x_7275_, v_size_7276_);
v___x_7306_ = lean_nat_add(v___x_7305_, v_size_7277_);
lean_dec(v_size_7277_);
if (lean_obj_tag(v_l_7296_) == 0)
{
lean_object* v_size_7327_; 
v_size_7327_ = lean_ctor_get(v_l_7296_, 0);
lean_inc(v_size_7327_);
v___y_7319_ = v_size_7327_;
goto v___jp_7318_;
}
else
{
lean_object* v___x_7328_; 
v___x_7328_ = lean_unsigned_to_nat(0u);
v___y_7319_ = v___x_7328_;
goto v___jp_7318_;
}
v___jp_7307_:
{
lean_object* v___x_7311_; lean_object* v___x_7313_; 
v___x_7311_ = lean_nat_add(v___y_7309_, v___y_7310_);
lean_dec(v___y_7310_);
lean_dec(v___y_7309_);
if (v_isShared_7304_ == 0)
{
lean_ctor_set(v___x_7303_, 4, v_r_7281_);
lean_ctor_set(v___x_7303_, 3, v_r_7297_);
lean_ctor_set(v___x_7303_, 2, v_v_7279_);
lean_ctor_set(v___x_7303_, 1, v_k_7278_);
lean_ctor_set(v___x_7303_, 0, v___x_7311_);
v___x_7313_ = v___x_7303_;
goto v_reusejp_7312_;
}
else
{
lean_object* v_reuseFailAlloc_7317_; 
v_reuseFailAlloc_7317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7317_, 0, v___x_7311_);
lean_ctor_set(v_reuseFailAlloc_7317_, 1, v_k_7278_);
lean_ctor_set(v_reuseFailAlloc_7317_, 2, v_v_7279_);
lean_ctor_set(v_reuseFailAlloc_7317_, 3, v_r_7297_);
lean_ctor_set(v_reuseFailAlloc_7317_, 4, v_r_7281_);
v___x_7313_ = v_reuseFailAlloc_7317_;
goto v_reusejp_7312_;
}
v_reusejp_7312_:
{
lean_object* v___x_7315_; 
if (v_isShared_7292_ == 0)
{
lean_ctor_set(v___x_7291_, 4, v___x_7313_);
lean_ctor_set(v___x_7291_, 3, v___y_7308_);
lean_ctor_set(v___x_7291_, 2, v_v_7295_);
lean_ctor_set(v___x_7291_, 1, v_k_7294_);
lean_ctor_set(v___x_7291_, 0, v___x_7306_);
v___x_7315_ = v___x_7291_;
goto v_reusejp_7314_;
}
else
{
lean_object* v_reuseFailAlloc_7316_; 
v_reuseFailAlloc_7316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7316_, 0, v___x_7306_);
lean_ctor_set(v_reuseFailAlloc_7316_, 1, v_k_7294_);
lean_ctor_set(v_reuseFailAlloc_7316_, 2, v_v_7295_);
lean_ctor_set(v_reuseFailAlloc_7316_, 3, v___y_7308_);
lean_ctor_set(v_reuseFailAlloc_7316_, 4, v___x_7313_);
v___x_7315_ = v_reuseFailAlloc_7316_;
goto v_reusejp_7314_;
}
v_reusejp_7314_:
{
return v___x_7315_;
}
}
}
v___jp_7318_:
{
lean_object* v___x_7320_; lean_object* v___x_7322_; 
v___x_7320_ = lean_nat_add(v___x_7305_, v___y_7319_);
lean_dec(v___y_7319_);
lean_dec(v___x_7305_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_l_7296_);
lean_ctor_set(v___x_7131_, 0, v___x_7320_);
v___x_7322_ = v___x_7131_;
goto v_reusejp_7321_;
}
else
{
lean_object* v_reuseFailAlloc_7326_; 
v_reuseFailAlloc_7326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7326_, 0, v___x_7320_);
lean_ctor_set(v_reuseFailAlloc_7326_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7326_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7326_, 3, v_l_7128_);
lean_ctor_set(v_reuseFailAlloc_7326_, 4, v_l_7296_);
v___x_7322_ = v_reuseFailAlloc_7326_;
goto v_reusejp_7321_;
}
v_reusejp_7321_:
{
lean_object* v___x_7323_; 
v___x_7323_ = lean_nat_add(v___x_7275_, v_size_7298_);
if (lean_obj_tag(v_r_7297_) == 0)
{
lean_object* v_size_7324_; 
v_size_7324_ = lean_ctor_get(v_r_7297_, 0);
lean_inc(v_size_7324_);
v___y_7308_ = v___x_7322_;
v___y_7309_ = v___x_7323_;
v___y_7310_ = v_size_7324_;
goto v___jp_7307_;
}
else
{
lean_object* v___x_7325_; 
v___x_7325_ = lean_unsigned_to_nat(0u);
v___y_7308_ = v___x_7322_;
v___y_7309_ = v___x_7323_;
v___y_7310_ = v___x_7325_;
goto v___jp_7307_;
}
}
}
}
}
else
{
lean_object* v___x_7335_; lean_object* v___x_7336_; lean_object* v___x_7337_; lean_object* v___x_7339_; 
lean_del_object(v___x_7131_);
v___x_7335_ = lean_nat_add(v___x_7275_, v_size_7276_);
v___x_7336_ = lean_nat_add(v___x_7335_, v_size_7277_);
lean_dec(v_size_7277_);
v___x_7337_ = lean_nat_add(v___x_7335_, v_size_7293_);
lean_dec(v___x_7335_);
lean_inc_ref(v_l_7128_);
if (v_isShared_7292_ == 0)
{
lean_ctor_set(v___x_7291_, 4, v_l_7280_);
lean_ctor_set(v___x_7291_, 3, v_l_7128_);
lean_ctor_set(v___x_7291_, 2, v_v_7127_);
lean_ctor_set(v___x_7291_, 1, v_k_7126_);
lean_ctor_set(v___x_7291_, 0, v___x_7337_);
v___x_7339_ = v___x_7291_;
goto v_reusejp_7338_;
}
else
{
lean_object* v_reuseFailAlloc_7352_; 
v_reuseFailAlloc_7352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7352_, 0, v___x_7337_);
lean_ctor_set(v_reuseFailAlloc_7352_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7352_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7352_, 3, v_l_7128_);
lean_ctor_set(v_reuseFailAlloc_7352_, 4, v_l_7280_);
v___x_7339_ = v_reuseFailAlloc_7352_;
goto v_reusejp_7338_;
}
v_reusejp_7338_:
{
lean_object* v___x_7341_; uint8_t v_isShared_7342_; uint8_t v_isSharedCheck_7346_; 
v_isSharedCheck_7346_ = !lean_is_exclusive(v_l_7128_);
if (v_isSharedCheck_7346_ == 0)
{
lean_object* v_unused_7347_; lean_object* v_unused_7348_; lean_object* v_unused_7349_; lean_object* v_unused_7350_; lean_object* v_unused_7351_; 
v_unused_7347_ = lean_ctor_get(v_l_7128_, 4);
lean_dec(v_unused_7347_);
v_unused_7348_ = lean_ctor_get(v_l_7128_, 3);
lean_dec(v_unused_7348_);
v_unused_7349_ = lean_ctor_get(v_l_7128_, 2);
lean_dec(v_unused_7349_);
v_unused_7350_ = lean_ctor_get(v_l_7128_, 1);
lean_dec(v_unused_7350_);
v_unused_7351_ = lean_ctor_get(v_l_7128_, 0);
lean_dec(v_unused_7351_);
v___x_7341_ = v_l_7128_;
v_isShared_7342_ = v_isSharedCheck_7346_;
goto v_resetjp_7340_;
}
else
{
lean_dec(v_l_7128_);
v___x_7341_ = lean_box(0);
v_isShared_7342_ = v_isSharedCheck_7346_;
goto v_resetjp_7340_;
}
v_resetjp_7340_:
{
lean_object* v___x_7344_; 
if (v_isShared_7342_ == 0)
{
lean_ctor_set(v___x_7341_, 4, v_r_7281_);
lean_ctor_set(v___x_7341_, 3, v___x_7339_);
lean_ctor_set(v___x_7341_, 2, v_v_7279_);
lean_ctor_set(v___x_7341_, 1, v_k_7278_);
lean_ctor_set(v___x_7341_, 0, v___x_7336_);
v___x_7344_ = v___x_7341_;
goto v_reusejp_7343_;
}
else
{
lean_object* v_reuseFailAlloc_7345_; 
v_reuseFailAlloc_7345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7345_, 0, v___x_7336_);
lean_ctor_set(v_reuseFailAlloc_7345_, 1, v_k_7278_);
lean_ctor_set(v_reuseFailAlloc_7345_, 2, v_v_7279_);
lean_ctor_set(v_reuseFailAlloc_7345_, 3, v___x_7339_);
lean_ctor_set(v_reuseFailAlloc_7345_, 4, v_r_7281_);
v___x_7344_ = v_reuseFailAlloc_7345_;
goto v_reusejp_7343_;
}
v_reusejp_7343_:
{
return v___x_7344_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7359_; 
v_l_7359_ = lean_ctor_get(v_impl_7274_, 3);
lean_inc(v_l_7359_);
if (lean_obj_tag(v_l_7359_) == 0)
{
lean_object* v_r_7360_; lean_object* v_k_7361_; lean_object* v_v_7362_; lean_object* v___x_7364_; uint8_t v_isShared_7365_; uint8_t v_isSharedCheck_7385_; 
v_r_7360_ = lean_ctor_get(v_impl_7274_, 4);
v_k_7361_ = lean_ctor_get(v_impl_7274_, 1);
v_v_7362_ = lean_ctor_get(v_impl_7274_, 2);
v_isSharedCheck_7385_ = !lean_is_exclusive(v_impl_7274_);
if (v_isSharedCheck_7385_ == 0)
{
lean_object* v_unused_7386_; lean_object* v_unused_7387_; 
v_unused_7386_ = lean_ctor_get(v_impl_7274_, 3);
lean_dec(v_unused_7386_);
v_unused_7387_ = lean_ctor_get(v_impl_7274_, 0);
lean_dec(v_unused_7387_);
v___x_7364_ = v_impl_7274_;
v_isShared_7365_ = v_isSharedCheck_7385_;
goto v_resetjp_7363_;
}
else
{
lean_inc(v_r_7360_);
lean_inc(v_v_7362_);
lean_inc(v_k_7361_);
lean_dec(v_impl_7274_);
v___x_7364_ = lean_box(0);
v_isShared_7365_ = v_isSharedCheck_7385_;
goto v_resetjp_7363_;
}
v_resetjp_7363_:
{
lean_object* v_k_7366_; lean_object* v_v_7367_; lean_object* v___x_7369_; uint8_t v_isShared_7370_; uint8_t v_isSharedCheck_7381_; 
v_k_7366_ = lean_ctor_get(v_l_7359_, 1);
v_v_7367_ = lean_ctor_get(v_l_7359_, 2);
v_isSharedCheck_7381_ = !lean_is_exclusive(v_l_7359_);
if (v_isSharedCheck_7381_ == 0)
{
lean_object* v_unused_7382_; lean_object* v_unused_7383_; lean_object* v_unused_7384_; 
v_unused_7382_ = lean_ctor_get(v_l_7359_, 4);
lean_dec(v_unused_7382_);
v_unused_7383_ = lean_ctor_get(v_l_7359_, 3);
lean_dec(v_unused_7383_);
v_unused_7384_ = lean_ctor_get(v_l_7359_, 0);
lean_dec(v_unused_7384_);
v___x_7369_ = v_l_7359_;
v_isShared_7370_ = v_isSharedCheck_7381_;
goto v_resetjp_7368_;
}
else
{
lean_inc(v_v_7367_);
lean_inc(v_k_7366_);
lean_dec(v_l_7359_);
v___x_7369_ = lean_box(0);
v_isShared_7370_ = v_isSharedCheck_7381_;
goto v_resetjp_7368_;
}
v_resetjp_7368_:
{
lean_object* v___x_7371_; lean_object* v___x_7373_; 
v___x_7371_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7360_, 2);
if (v_isShared_7370_ == 0)
{
lean_ctor_set(v___x_7369_, 4, v_r_7360_);
lean_ctor_set(v___x_7369_, 3, v_r_7360_);
lean_ctor_set(v___x_7369_, 2, v_v_7127_);
lean_ctor_set(v___x_7369_, 1, v_k_7126_);
lean_ctor_set(v___x_7369_, 0, v___x_7275_);
v___x_7373_ = v___x_7369_;
goto v_reusejp_7372_;
}
else
{
lean_object* v_reuseFailAlloc_7380_; 
v_reuseFailAlloc_7380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7380_, 0, v___x_7275_);
lean_ctor_set(v_reuseFailAlloc_7380_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7380_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7380_, 3, v_r_7360_);
lean_ctor_set(v_reuseFailAlloc_7380_, 4, v_r_7360_);
v___x_7373_ = v_reuseFailAlloc_7380_;
goto v_reusejp_7372_;
}
v_reusejp_7372_:
{
lean_object* v___x_7375_; 
lean_inc(v_r_7360_);
if (v_isShared_7365_ == 0)
{
lean_ctor_set(v___x_7364_, 3, v_r_7360_);
lean_ctor_set(v___x_7364_, 0, v___x_7275_);
v___x_7375_ = v___x_7364_;
goto v_reusejp_7374_;
}
else
{
lean_object* v_reuseFailAlloc_7379_; 
v_reuseFailAlloc_7379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7379_, 0, v___x_7275_);
lean_ctor_set(v_reuseFailAlloc_7379_, 1, v_k_7361_);
lean_ctor_set(v_reuseFailAlloc_7379_, 2, v_v_7362_);
lean_ctor_set(v_reuseFailAlloc_7379_, 3, v_r_7360_);
lean_ctor_set(v_reuseFailAlloc_7379_, 4, v_r_7360_);
v___x_7375_ = v_reuseFailAlloc_7379_;
goto v_reusejp_7374_;
}
v_reusejp_7374_:
{
lean_object* v___x_7377_; 
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v___x_7375_);
lean_ctor_set(v___x_7131_, 3, v___x_7373_);
lean_ctor_set(v___x_7131_, 2, v_v_7367_);
lean_ctor_set(v___x_7131_, 1, v_k_7366_);
lean_ctor_set(v___x_7131_, 0, v___x_7371_);
v___x_7377_ = v___x_7131_;
goto v_reusejp_7376_;
}
else
{
lean_object* v_reuseFailAlloc_7378_; 
v_reuseFailAlloc_7378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7378_, 0, v___x_7371_);
lean_ctor_set(v_reuseFailAlloc_7378_, 1, v_k_7366_);
lean_ctor_set(v_reuseFailAlloc_7378_, 2, v_v_7367_);
lean_ctor_set(v_reuseFailAlloc_7378_, 3, v___x_7373_);
lean_ctor_set(v_reuseFailAlloc_7378_, 4, v___x_7375_);
v___x_7377_ = v_reuseFailAlloc_7378_;
goto v_reusejp_7376_;
}
v_reusejp_7376_:
{
return v___x_7377_;
}
}
}
}
}
}
else
{
lean_object* v_r_7388_; 
v_r_7388_ = lean_ctor_get(v_impl_7274_, 4);
lean_inc(v_r_7388_);
if (lean_obj_tag(v_r_7388_) == 0)
{
lean_object* v_k_7389_; lean_object* v_v_7390_; lean_object* v___x_7392_; uint8_t v_isShared_7393_; uint8_t v_isSharedCheck_7401_; 
v_k_7389_ = lean_ctor_get(v_impl_7274_, 1);
v_v_7390_ = lean_ctor_get(v_impl_7274_, 2);
v_isSharedCheck_7401_ = !lean_is_exclusive(v_impl_7274_);
if (v_isSharedCheck_7401_ == 0)
{
lean_object* v_unused_7402_; lean_object* v_unused_7403_; lean_object* v_unused_7404_; 
v_unused_7402_ = lean_ctor_get(v_impl_7274_, 4);
lean_dec(v_unused_7402_);
v_unused_7403_ = lean_ctor_get(v_impl_7274_, 3);
lean_dec(v_unused_7403_);
v_unused_7404_ = lean_ctor_get(v_impl_7274_, 0);
lean_dec(v_unused_7404_);
v___x_7392_ = v_impl_7274_;
v_isShared_7393_ = v_isSharedCheck_7401_;
goto v_resetjp_7391_;
}
else
{
lean_inc(v_v_7390_);
lean_inc(v_k_7389_);
lean_dec(v_impl_7274_);
v___x_7392_ = lean_box(0);
v_isShared_7393_ = v_isSharedCheck_7401_;
goto v_resetjp_7391_;
}
v_resetjp_7391_:
{
lean_object* v___x_7394_; lean_object* v___x_7396_; 
v___x_7394_ = lean_unsigned_to_nat(3u);
if (v_isShared_7393_ == 0)
{
lean_ctor_set(v___x_7392_, 4, v_l_7359_);
lean_ctor_set(v___x_7392_, 2, v_v_7127_);
lean_ctor_set(v___x_7392_, 1, v_k_7126_);
lean_ctor_set(v___x_7392_, 0, v___x_7275_);
v___x_7396_ = v___x_7392_;
goto v_reusejp_7395_;
}
else
{
lean_object* v_reuseFailAlloc_7400_; 
v_reuseFailAlloc_7400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7400_, 0, v___x_7275_);
lean_ctor_set(v_reuseFailAlloc_7400_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7400_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7400_, 3, v_l_7359_);
lean_ctor_set(v_reuseFailAlloc_7400_, 4, v_l_7359_);
v___x_7396_ = v_reuseFailAlloc_7400_;
goto v_reusejp_7395_;
}
v_reusejp_7395_:
{
lean_object* v___x_7398_; 
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_r_7388_);
lean_ctor_set(v___x_7131_, 3, v___x_7396_);
lean_ctor_set(v___x_7131_, 2, v_v_7390_);
lean_ctor_set(v___x_7131_, 1, v_k_7389_);
lean_ctor_set(v___x_7131_, 0, v___x_7394_);
v___x_7398_ = v___x_7131_;
goto v_reusejp_7397_;
}
else
{
lean_object* v_reuseFailAlloc_7399_; 
v_reuseFailAlloc_7399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7399_, 0, v___x_7394_);
lean_ctor_set(v_reuseFailAlloc_7399_, 1, v_k_7389_);
lean_ctor_set(v_reuseFailAlloc_7399_, 2, v_v_7390_);
lean_ctor_set(v_reuseFailAlloc_7399_, 3, v___x_7396_);
lean_ctor_set(v_reuseFailAlloc_7399_, 4, v_r_7388_);
v___x_7398_ = v_reuseFailAlloc_7399_;
goto v_reusejp_7397_;
}
v_reusejp_7397_:
{
return v___x_7398_;
}
}
}
}
else
{
lean_object* v___x_7405_; lean_object* v___x_7407_; 
v___x_7405_ = lean_unsigned_to_nat(2u);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 4, v_impl_7274_);
lean_ctor_set(v___x_7131_, 3, v_r_7388_);
lean_ctor_set(v___x_7131_, 0, v___x_7405_);
v___x_7407_ = v___x_7131_;
goto v_reusejp_7406_;
}
else
{
lean_object* v_reuseFailAlloc_7408_; 
v_reuseFailAlloc_7408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7408_, 0, v___x_7405_);
lean_ctor_set(v_reuseFailAlloc_7408_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7408_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7408_, 3, v_r_7388_);
lean_ctor_set(v_reuseFailAlloc_7408_, 4, v_impl_7274_);
v___x_7407_ = v_reuseFailAlloc_7408_;
goto v_reusejp_7406_;
}
v_reusejp_7406_:
{
return v___x_7407_;
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
lean_object* v___x_7410_; lean_object* v___x_7411_; 
v___x_7410_ = lean_unsigned_to_nat(1u);
v___x_7411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7411_, 0, v___x_7410_);
lean_ctor_set(v___x_7411_, 1, v_k_7122_);
lean_ctor_set(v___x_7411_, 2, v_v_7123_);
lean_ctor_set(v___x_7411_, 3, v_t_7124_);
lean_ctor_set(v___x_7411_, 4, v_t_7124_);
return v___x_7411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7412_, lean_object* v_ps_7413_, lean_object* v_v_7414_, lean_object* v_o_7415_){
_start:
{
lean_object* v_name_7416_; lean_object* v_deps_7417_; lean_object* v_o_7418_; uint8_t v___x_7419_; 
v_name_7416_ = lean_ctor_get(v_lib_7412_, 1);
lean_inc_ref(v_name_7416_);
v_deps_7417_ = lean_ctor_get(v_lib_7412_, 2);
lean_inc_ref(v_deps_7417_);
v_o_7418_ = lean_array_push(v_o_7415_, v_lib_7412_);
v___x_7419_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7416_, v_v_7414_);
if (v___x_7419_ == 0)
{
uint8_t v___x_7420_; 
v___x_7420_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7416_, v_ps_7413_);
if (v___x_7420_ == 0)
{
lean_object* v_ps_7421_; lean_object* v___y_7423_; 
lean_inc_ref(v_name_7416_);
v_ps_7421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7421_, 0, v_name_7416_);
lean_ctor_set(v_ps_7421_, 1, v_ps_7413_);
if (v___x_7419_ == 0)
{
lean_object* v___x_7437_; lean_object* v___x_7438_; 
v___x_7437_ = lean_box(0);
v___x_7438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7416_, v___x_7437_, v_v_7414_);
v___y_7423_ = v___x_7438_;
goto v___jp_7422_;
}
else
{
lean_dec_ref(v_name_7416_);
v___y_7423_ = v_v_7414_;
goto v___jp_7422_;
}
v___jp_7422_:
{
lean_object* v___x_7424_; lean_object* v___x_7425_; lean_object* v___x_7426_; uint8_t v___x_7427_; 
v___x_7424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7424_, 0, v___y_7423_);
lean_ctor_set(v___x_7424_, 1, v_o_7418_);
v___x_7425_ = lean_unsigned_to_nat(0u);
v___x_7426_ = lean_array_get_size(v_deps_7417_);
v___x_7427_ = lean_nat_dec_lt(v___x_7425_, v___x_7426_);
if (v___x_7427_ == 0)
{
lean_object* v___x_7428_; 
lean_dec_ref_known(v_ps_7421_, 2);
lean_dec_ref(v_deps_7417_);
v___x_7428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7428_, 0, v___x_7424_);
return v___x_7428_;
}
else
{
uint8_t v___x_7429_; 
v___x_7429_ = lean_nat_dec_le(v___x_7426_, v___x_7426_);
if (v___x_7429_ == 0)
{
if (v___x_7427_ == 0)
{
lean_object* v___x_7430_; 
lean_dec_ref_known(v_ps_7421_, 2);
lean_dec_ref(v_deps_7417_);
v___x_7430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7430_, 0, v___x_7424_);
return v___x_7430_;
}
else
{
size_t v___x_7431_; size_t v___x_7432_; lean_object* v___x_7433_; 
v___x_7431_ = ((size_t)0ULL);
v___x_7432_ = lean_usize_of_nat(v___x_7426_);
v___x_7433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7421_, v_deps_7417_, v___x_7431_, v___x_7432_, v___x_7424_);
lean_dec_ref(v_deps_7417_);
return v___x_7433_;
}
}
else
{
size_t v___x_7434_; size_t v___x_7435_; lean_object* v___x_7436_; 
v___x_7434_ = ((size_t)0ULL);
v___x_7435_ = lean_usize_of_nat(v___x_7426_);
v___x_7436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7421_, v_deps_7417_, v___x_7434_, v___x_7435_, v___x_7424_);
lean_dec_ref(v_deps_7417_);
return v___x_7436_;
}
}
}
}
else
{
lean_object* v___x_7439_; lean_object* v___x_7440_; 
lean_dec_ref(v_o_7418_);
lean_dec_ref(v_deps_7417_);
lean_dec(v_v_7414_);
v___x_7439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7439_, 0, v_name_7416_);
lean_ctor_set(v___x_7439_, 1, v_ps_7413_);
v___x_7440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7440_, 0, v___x_7439_);
return v___x_7440_;
}
}
else
{
lean_object* v___x_7441_; lean_object* v___x_7442_; 
lean_dec_ref(v_deps_7417_);
lean_dec_ref(v_name_7416_);
lean_dec(v_ps_7413_);
v___x_7441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7441_, 0, v_v_7414_);
lean_ctor_set(v___x_7441_, 1, v_o_7418_);
v___x_7442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7442_, 0, v___x_7441_);
return v___x_7442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7443_, lean_object* v_as_7444_, size_t v_i_7445_, size_t v_stop_7446_, lean_object* v_b_7447_){
_start:
{
uint8_t v___x_7448_; 
v___x_7448_ = lean_usize_dec_eq(v_i_7445_, v_stop_7446_);
if (v___x_7448_ == 0)
{
lean_object* v_fst_7449_; lean_object* v_snd_7450_; lean_object* v___x_7451_; lean_object* v___x_7452_; 
v_fst_7449_ = lean_ctor_get(v_b_7447_, 0);
lean_inc(v_fst_7449_);
v_snd_7450_ = lean_ctor_get(v_b_7447_, 1);
lean_inc(v_snd_7450_);
lean_dec_ref(v_b_7447_);
v___x_7451_ = lean_array_uget_borrowed(v_as_7444_, v_i_7445_);
lean_inc(v_ps_7443_);
lean_inc(v___x_7451_);
v___x_7452_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7451_, v_ps_7443_, v_fst_7449_, v_snd_7450_);
if (lean_obj_tag(v___x_7452_) == 0)
{
lean_dec(v_ps_7443_);
return v___x_7452_;
}
else
{
lean_object* v_a_7453_; size_t v___x_7454_; size_t v___x_7455_; 
v_a_7453_ = lean_ctor_get(v___x_7452_, 0);
lean_inc(v_a_7453_);
lean_dec_ref_known(v___x_7452_, 1);
v___x_7454_ = ((size_t)1ULL);
v___x_7455_ = lean_usize_add(v_i_7445_, v___x_7454_);
v_i_7445_ = v___x_7455_;
v_b_7447_ = v_a_7453_;
goto _start;
}
}
else
{
lean_object* v___x_7457_; 
lean_dec(v_ps_7443_);
v___x_7457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7457_, 0, v_b_7447_);
return v___x_7457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7458_, lean_object* v_as_7459_, lean_object* v_i_7460_, lean_object* v_stop_7461_, lean_object* v_b_7462_){
_start:
{
size_t v_i_boxed_7463_; size_t v_stop_boxed_7464_; lean_object* v_res_7465_; 
v_i_boxed_7463_ = lean_unbox_usize(v_i_7460_);
lean_dec(v_i_7460_);
v_stop_boxed_7464_ = lean_unbox_usize(v_stop_7461_);
lean_dec(v_stop_7461_);
v_res_7465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7458_, v_as_7459_, v_i_boxed_7463_, v_stop_boxed_7464_, v_b_7462_);
lean_dec_ref(v_as_7459_);
return v_res_7465_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7466_, lean_object* v_k_7467_, lean_object* v_t_7468_){
_start:
{
uint8_t v___x_7469_; 
v___x_7469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7467_, v_t_7468_);
return v___x_7469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7470_, lean_object* v_k_7471_, lean_object* v_t_7472_){
_start:
{
uint8_t v_res_7473_; lean_object* v_r_7474_; 
v_res_7473_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7470_, v_k_7471_, v_t_7472_);
lean_dec(v_t_7472_);
lean_dec_ref(v_k_7471_);
v_r_7474_ = lean_box(v_res_7473_);
return v_r_7474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7475_, lean_object* v_k_7476_, lean_object* v_v_7477_, lean_object* v_t_7478_, lean_object* v_hl_7479_){
_start:
{
lean_object* v___x_7480_; 
v___x_7480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7476_, v_v_7477_, v_t_7478_);
return v___x_7480_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7482_, lean_object* v_a_7483_){
_start:
{
if (lean_obj_tag(v_a_7482_) == 0)
{
lean_object* v___x_7484_; 
v___x_7484_ = l_List_reverse___redArg(v_a_7483_);
return v___x_7484_;
}
else
{
lean_object* v_head_7485_; lean_object* v_tail_7486_; lean_object* v___x_7488_; uint8_t v_isShared_7489_; uint8_t v_isSharedCheck_7496_; 
v_head_7485_ = lean_ctor_get(v_a_7482_, 0);
v_tail_7486_ = lean_ctor_get(v_a_7482_, 1);
v_isSharedCheck_7496_ = !lean_is_exclusive(v_a_7482_);
if (v_isSharedCheck_7496_ == 0)
{
v___x_7488_ = v_a_7482_;
v_isShared_7489_ = v_isSharedCheck_7496_;
goto v_resetjp_7487_;
}
else
{
lean_inc(v_tail_7486_);
lean_inc(v_head_7485_);
lean_dec(v_a_7482_);
v___x_7488_ = lean_box(0);
v_isShared_7489_ = v_isSharedCheck_7496_;
goto v_resetjp_7487_;
}
v_resetjp_7487_:
{
lean_object* v___x_7490_; lean_object* v___x_7491_; lean_object* v___x_7493_; 
v___x_7490_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7491_ = lean_string_append(v___x_7490_, v_head_7485_);
lean_dec(v_head_7485_);
if (v_isShared_7489_ == 0)
{
lean_ctor_set(v___x_7488_, 1, v_a_7483_);
lean_ctor_set(v___x_7488_, 0, v___x_7491_);
v___x_7493_ = v___x_7488_;
goto v_reusejp_7492_;
}
else
{
lean_object* v_reuseFailAlloc_7495_; 
v_reuseFailAlloc_7495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7495_, 0, v___x_7491_);
lean_ctor_set(v_reuseFailAlloc_7495_, 1, v_a_7483_);
v___x_7493_ = v_reuseFailAlloc_7495_;
goto v_reusejp_7492_;
}
v_reusejp_7492_:
{
v_a_7482_ = v_tail_7486_;
v_a_7483_ = v___x_7493_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7497_){
_start:
{
lean_object* v___x_7498_; lean_object* v___x_7499_; lean_object* v___x_7500_; lean_object* v___x_7501_; 
v___x_7498_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7499_ = lean_box(0);
v___x_7500_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7497_, v___x_7499_);
v___x_7501_ = l_String_intercalate(v___x_7498_, v___x_7500_);
return v___x_7501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object* v_as_7502_, size_t v_i_7503_, size_t v_stop_7504_, lean_object* v_b_7505_){
_start:
{
uint8_t v___x_7506_; 
v___x_7506_ = lean_usize_dec_eq(v_i_7503_, v_stop_7504_);
if (v___x_7506_ == 0)
{
lean_object* v_fst_7507_; lean_object* v_snd_7508_; lean_object* v___x_7509_; lean_object* v___x_7510_; lean_object* v___x_7511_; 
v_fst_7507_ = lean_ctor_get(v_b_7505_, 0);
lean_inc(v_fst_7507_);
v_snd_7508_ = lean_ctor_get(v_b_7505_, 1);
lean_inc(v_snd_7508_);
lean_dec_ref(v_b_7505_);
v___x_7509_ = lean_array_uget_borrowed(v_as_7502_, v_i_7503_);
v___x_7510_ = lean_box(0);
lean_inc(v___x_7509_);
v___x_7511_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7509_, v___x_7510_, v_fst_7507_, v_snd_7508_);
if (lean_obj_tag(v___x_7511_) == 0)
{
return v___x_7511_;
}
else
{
lean_object* v_a_7512_; size_t v___x_7513_; size_t v___x_7514_; 
v_a_7512_ = lean_ctor_get(v___x_7511_, 0);
lean_inc(v_a_7512_);
lean_dec_ref_known(v___x_7511_, 1);
v___x_7513_ = ((size_t)1ULL);
v___x_7514_ = lean_usize_add(v_i_7503_, v___x_7513_);
v_i_7503_ = v___x_7514_;
v_b_7505_ = v_a_7512_;
goto _start;
}
}
else
{
lean_object* v___x_7516_; 
v___x_7516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7516_, 0, v_b_7505_);
return v___x_7516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7517_, lean_object* v_i_7518_, lean_object* v_stop_7519_, lean_object* v_b_7520_){
_start:
{
size_t v_i_boxed_7521_; size_t v_stop_boxed_7522_; lean_object* v_res_7523_; 
v_i_boxed_7521_ = lean_unbox_usize(v_i_7518_);
lean_dec(v_i_7518_);
v_stop_boxed_7522_ = lean_unbox_usize(v_stop_7519_);
lean_dec(v_stop_7519_);
v_res_7523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_as_7517_, v_i_boxed_7521_, v_stop_boxed_7522_, v_b_7520_);
lean_dec_ref(v_as_7517_);
return v_res_7523_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object* v_libs_7530_, lean_object* v_a_7531_){
_start:
{
lean_object* v_snd_7534_; lean_object* v___y_7537_; lean_object* v___x_7561_; lean_object* v___x_7562_; lean_object* v___x_7563_; uint8_t v___x_7564_; 
v___x_7561_ = lean_unsigned_to_nat(0u);
v___x_7562_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7563_ = lean_array_get_size(v_libs_7530_);
v___x_7564_ = lean_nat_dec_lt(v___x_7561_, v___x_7563_);
if (v___x_7564_ == 0)
{
v_snd_7534_ = v___x_7562_;
goto v___jp_7533_;
}
else
{
lean_object* v___x_7565_; uint8_t v___x_7566_; 
v___x_7565_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__2));
v___x_7566_ = lean_nat_dec_le(v___x_7563_, v___x_7563_);
if (v___x_7566_ == 0)
{
if (v___x_7564_ == 0)
{
v_snd_7534_ = v___x_7562_;
goto v___jp_7533_;
}
else
{
size_t v___x_7567_; size_t v___x_7568_; lean_object* v___x_7569_; 
v___x_7567_ = ((size_t)0ULL);
v___x_7568_ = lean_usize_of_nat(v___x_7563_);
v___x_7569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7530_, v___x_7567_, v___x_7568_, v___x_7565_);
v___y_7537_ = v___x_7569_;
goto v___jp_7536_;
}
}
else
{
size_t v___x_7570_; size_t v___x_7571_; lean_object* v___x_7572_; 
v___x_7570_ = ((size_t)0ULL);
v___x_7571_ = lean_usize_of_nat(v___x_7563_);
v___x_7572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7530_, v___x_7570_, v___x_7571_, v___x_7565_);
v___y_7537_ = v___x_7572_;
goto v___jp_7536_;
}
}
v___jp_7533_:
{
lean_object* v___x_7535_; 
v___x_7535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7535_, 0, v_snd_7534_);
lean_ctor_set(v___x_7535_, 1, v_a_7531_);
return v___x_7535_;
}
v___jp_7536_:
{
if (lean_obj_tag(v___y_7537_) == 0)
{
lean_object* v_a_7538_; lean_object* v_log_7539_; uint8_t v_action_7540_; uint8_t v_wantsRebuild_7541_; lean_object* v_trace_7542_; lean_object* v_buildTime_7543_; lean_object* v___x_7545_; uint8_t v_isShared_7546_; uint8_t v_isSharedCheck_7558_; 
v_a_7538_ = lean_ctor_get(v___y_7537_, 0);
lean_inc(v_a_7538_);
lean_dec_ref_known(v___y_7537_, 1);
v_log_7539_ = lean_ctor_get(v_a_7531_, 0);
v_action_7540_ = lean_ctor_get_uint8(v_a_7531_, sizeof(void*)*3);
v_wantsRebuild_7541_ = lean_ctor_get_uint8(v_a_7531_, sizeof(void*)*3 + 1);
v_trace_7542_ = lean_ctor_get(v_a_7531_, 1);
v_buildTime_7543_ = lean_ctor_get(v_a_7531_, 2);
v_isSharedCheck_7558_ = !lean_is_exclusive(v_a_7531_);
if (v_isSharedCheck_7558_ == 0)
{
v___x_7545_ = v_a_7531_;
v_isShared_7546_ = v_isSharedCheck_7558_;
goto v_resetjp_7544_;
}
else
{
lean_inc(v_buildTime_7543_);
lean_inc(v_trace_7542_);
lean_inc(v_log_7539_);
lean_dec(v_a_7531_);
v___x_7545_ = lean_box(0);
v_isShared_7546_ = v_isSharedCheck_7558_;
goto v_resetjp_7544_;
}
v_resetjp_7544_:
{
lean_object* v___x_7547_; lean_object* v___x_7548_; lean_object* v___x_7549_; uint8_t v___x_7550_; lean_object* v___x_7551_; lean_object* v___x_7552_; lean_object* v___x_7553_; lean_object* v___x_7555_; 
v___x_7547_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__0));
v___x_7548_ = l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(v_a_7538_);
v___x_7549_ = lean_string_append(v___x_7547_, v___x_7548_);
lean_dec_ref(v___x_7548_);
v___x_7550_ = 3;
v___x_7551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7551_, 0, v___x_7549_);
lean_ctor_set_uint8(v___x_7551_, sizeof(void*)*1, v___x_7550_);
v___x_7552_ = lean_array_get_size(v_log_7539_);
v___x_7553_ = lean_array_push(v_log_7539_, v___x_7551_);
if (v_isShared_7546_ == 0)
{
lean_ctor_set(v___x_7545_, 0, v___x_7553_);
v___x_7555_ = v___x_7545_;
goto v_reusejp_7554_;
}
else
{
lean_object* v_reuseFailAlloc_7557_; 
v_reuseFailAlloc_7557_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7557_, 0, v___x_7553_);
lean_ctor_set(v_reuseFailAlloc_7557_, 1, v_trace_7542_);
lean_ctor_set(v_reuseFailAlloc_7557_, 2, v_buildTime_7543_);
lean_ctor_set_uint8(v_reuseFailAlloc_7557_, sizeof(void*)*3, v_action_7540_);
lean_ctor_set_uint8(v_reuseFailAlloc_7557_, sizeof(void*)*3 + 1, v_wantsRebuild_7541_);
v___x_7555_ = v_reuseFailAlloc_7557_;
goto v_reusejp_7554_;
}
v_reusejp_7554_:
{
lean_object* v___x_7556_; 
v___x_7556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7556_, 0, v___x_7552_);
lean_ctor_set(v___x_7556_, 1, v___x_7555_);
return v___x_7556_;
}
}
}
else
{
lean_object* v_a_7559_; lean_object* v_snd_7560_; 
v_a_7559_ = lean_ctor_get(v___y_7537_, 0);
lean_inc(v_a_7559_);
lean_dec_ref_known(v___y_7537_, 1);
v_snd_7560_ = lean_ctor_get(v_a_7559_, 1);
lean_inc(v_snd_7560_);
lean_dec(v_a_7559_);
v_snd_7534_ = v_snd_7560_;
goto v___jp_7533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_){
_start:
{
lean_object* v_res_7576_; 
v_res_7576_ = l_Lake_mkLinkOrder___redArg(v_libs_7573_, v_a_7574_);
lean_dec_ref(v_libs_7573_);
return v_res_7576_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object* v_libs_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_){
_start:
{
lean_object* v___x_7585_; 
v___x_7585_ = l_Lake_mkLinkOrder___redArg(v_libs_7577_, v_a_7583_);
return v___x_7585_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object* v_libs_7586_, lean_object* v_a_7587_, lean_object* v_a_7588_, lean_object* v_a_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_){
_start:
{
lean_object* v_res_7594_; 
v_res_7594_ = l_Lake_mkLinkOrder(v_libs_7586_, v_a_7587_, v_a_7588_, v_a_7589_, v_a_7590_, v_a_7591_, v_a_7592_);
lean_dec_ref(v_a_7591_);
lean_dec(v_a_7590_);
lean_dec(v_a_7589_);
lean_dec(v_a_7588_);
lean_dec_ref(v_a_7587_);
lean_dec_ref(v_libs_7586_);
return v_res_7594_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object* v_objs_7595_, lean_object* v_libs_7596_, uint8_t v_linkDeps_7597_, lean_object* v_a_7598_){
_start:
{
lean_object* v_libs_7601_; lean_object* v___y_7602_; 
if (v_linkDeps_7597_ == 0)
{
lean_object* v___x_7605_; 
v___x_7605_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7601_ = v___x_7605_;
v___y_7602_ = v_a_7598_;
goto v___jp_7600_;
}
else
{
lean_object* v___x_7606_; 
v___x_7606_ = l_Lake_mkLinkOrder___redArg(v_libs_7596_, v_a_7598_);
if (lean_obj_tag(v___x_7606_) == 0)
{
lean_object* v_a_7607_; lean_object* v_a_7608_; 
v_a_7607_ = lean_ctor_get(v___x_7606_, 0);
lean_inc(v_a_7607_);
v_a_7608_ = lean_ctor_get(v___x_7606_, 1);
lean_inc(v_a_7608_);
lean_dec_ref_known(v___x_7606_, 2);
v_libs_7601_ = v_a_7607_;
v___y_7602_ = v_a_7608_;
goto v___jp_7600_;
}
else
{
lean_object* v_a_7609_; lean_object* v_a_7610_; lean_object* v___x_7612_; uint8_t v_isShared_7613_; uint8_t v_isSharedCheck_7617_; 
v_a_7609_ = lean_ctor_get(v___x_7606_, 0);
v_a_7610_ = lean_ctor_get(v___x_7606_, 1);
v_isSharedCheck_7617_ = !lean_is_exclusive(v___x_7606_);
if (v_isSharedCheck_7617_ == 0)
{
v___x_7612_ = v___x_7606_;
v_isShared_7613_ = v_isSharedCheck_7617_;
goto v_resetjp_7611_;
}
else
{
lean_inc(v_a_7610_);
lean_inc(v_a_7609_);
lean_dec(v___x_7606_);
v___x_7612_ = lean_box(0);
v_isShared_7613_ = v_isSharedCheck_7617_;
goto v_resetjp_7611_;
}
v_resetjp_7611_:
{
lean_object* v___x_7615_; 
if (v_isShared_7613_ == 0)
{
v___x_7615_ = v___x_7612_;
goto v_reusejp_7614_;
}
else
{
lean_object* v_reuseFailAlloc_7616_; 
v_reuseFailAlloc_7616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7616_, 0, v_a_7609_);
lean_ctor_set(v_reuseFailAlloc_7616_, 1, v_a_7610_);
v___x_7615_ = v_reuseFailAlloc_7616_;
goto v_reusejp_7614_;
}
v_reusejp_7614_:
{
return v___x_7615_;
}
}
}
}
v___jp_7600_:
{
lean_object* v___x_7603_; lean_object* v___x_7604_; 
v___x_7603_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7595_, v_libs_7601_);
lean_dec_ref(v_libs_7601_);
v___x_7604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7604_, 0, v___x_7603_);
lean_ctor_set(v___x_7604_, 1, v___y_7602_);
return v___x_7604_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object* v_objs_7618_, lean_object* v_libs_7619_, lean_object* v_linkDeps_7620_, lean_object* v_a_7621_, lean_object* v_a_7622_){
_start:
{
uint8_t v_linkDeps_boxed_7623_; lean_object* v_res_7624_; 
v_linkDeps_boxed_7623_ = lean_unbox(v_linkDeps_7620_);
v_res_7624_ = l_Lake_mkLinkArgs___redArg(v_objs_7618_, v_libs_7619_, v_linkDeps_boxed_7623_, v_a_7621_);
lean_dec_ref(v_libs_7619_);
lean_dec_ref(v_objs_7618_);
return v_res_7624_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object* v_objs_7625_, lean_object* v_libs_7626_, uint8_t v_linkDeps_7627_, lean_object* v_a_7628_, lean_object* v_a_7629_, lean_object* v_a_7630_, lean_object* v_a_7631_, lean_object* v_a_7632_, lean_object* v_a_7633_){
_start:
{
lean_object* v_libs_7636_; lean_object* v___y_7637_; 
if (v_linkDeps_7627_ == 0)
{
lean_object* v___x_7640_; 
v___x_7640_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7636_ = v___x_7640_;
v___y_7637_ = v_a_7633_;
goto v___jp_7635_;
}
else
{
lean_object* v___x_7641_; 
v___x_7641_ = l_Lake_mkLinkOrder___redArg(v_libs_7626_, v_a_7633_);
if (lean_obj_tag(v___x_7641_) == 0)
{
lean_object* v_a_7642_; lean_object* v_a_7643_; 
v_a_7642_ = lean_ctor_get(v___x_7641_, 0);
lean_inc(v_a_7642_);
v_a_7643_ = lean_ctor_get(v___x_7641_, 1);
lean_inc(v_a_7643_);
lean_dec_ref_known(v___x_7641_, 2);
v_libs_7636_ = v_a_7642_;
v___y_7637_ = v_a_7643_;
goto v___jp_7635_;
}
else
{
lean_object* v_a_7644_; lean_object* v_a_7645_; lean_object* v___x_7647_; uint8_t v_isShared_7648_; uint8_t v_isSharedCheck_7652_; 
v_a_7644_ = lean_ctor_get(v___x_7641_, 0);
v_a_7645_ = lean_ctor_get(v___x_7641_, 1);
v_isSharedCheck_7652_ = !lean_is_exclusive(v___x_7641_);
if (v_isSharedCheck_7652_ == 0)
{
v___x_7647_ = v___x_7641_;
v_isShared_7648_ = v_isSharedCheck_7652_;
goto v_resetjp_7646_;
}
else
{
lean_inc(v_a_7645_);
lean_inc(v_a_7644_);
lean_dec(v___x_7641_);
v___x_7647_ = lean_box(0);
v_isShared_7648_ = v_isSharedCheck_7652_;
goto v_resetjp_7646_;
}
v_resetjp_7646_:
{
lean_object* v___x_7650_; 
if (v_isShared_7648_ == 0)
{
v___x_7650_ = v___x_7647_;
goto v_reusejp_7649_;
}
else
{
lean_object* v_reuseFailAlloc_7651_; 
v_reuseFailAlloc_7651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7651_, 0, v_a_7644_);
lean_ctor_set(v_reuseFailAlloc_7651_, 1, v_a_7645_);
v___x_7650_ = v_reuseFailAlloc_7651_;
goto v_reusejp_7649_;
}
v_reusejp_7649_:
{
return v___x_7650_;
}
}
}
}
v___jp_7635_:
{
lean_object* v___x_7638_; lean_object* v___x_7639_; 
v___x_7638_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7625_, v_libs_7636_);
lean_dec_ref(v_libs_7636_);
v___x_7639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7639_, 0, v___x_7638_);
lean_ctor_set(v___x_7639_, 1, v___y_7637_);
return v___x_7639_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object* v_objs_7653_, lean_object* v_libs_7654_, lean_object* v_linkDeps_7655_, lean_object* v_a_7656_, lean_object* v_a_7657_, lean_object* v_a_7658_, lean_object* v_a_7659_, lean_object* v_a_7660_, lean_object* v_a_7661_, lean_object* v_a_7662_){
_start:
{
uint8_t v_linkDeps_boxed_7663_; lean_object* v_res_7664_; 
v_linkDeps_boxed_7663_ = lean_unbox(v_linkDeps_7655_);
v_res_7664_ = l_Lake_mkLinkArgs(v_objs_7653_, v_libs_7654_, v_linkDeps_boxed_7663_, v_a_7656_, v_a_7657_, v_a_7658_, v_a_7659_, v_a_7660_, v_a_7661_);
lean_dec_ref(v_a_7660_);
lean_dec(v_a_7659_);
lean_dec(v_a_7658_);
lean_dec(v_a_7657_);
lean_dec_ref(v_a_7656_);
lean_dec_ref(v_libs_7654_);
lean_dec_ref(v_objs_7653_);
return v_res_7664_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0(void){
_start:
{
lean_object* v___x_7665_; lean_object* v___x_7666_; lean_object* v___x_7667_; lean_object* v___x_7668_; 
v___x_7665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7666_ = lean_unsigned_to_nat(2u);
v___x_7667_ = lean_mk_empty_array_with_capacity(v___x_7666_);
v___x_7668_ = lean_array_push(v___x_7667_, v___x_7665_);
return v___x_7668_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object* v_objs_7669_, lean_object* v_libs_7670_, lean_object* v_args_7671_, uint8_t v_linkDeps_7672_, uint8_t v_sharedLean_7673_, lean_object* v_a_7674_, lean_object* v_a_7675_){
_start:
{
lean_object* v_toContext_7677_; lean_object* v_lakeEnv_7678_; lean_object* v_lean_7679_; lean_object* v_libs_7681_; lean_object* v___y_7682_; 
v_toContext_7677_ = lean_ctor_get(v_a_7674_, 1);
v_lakeEnv_7678_ = lean_ctor_get(v_toContext_7677_, 0);
v_lean_7679_ = lean_ctor_get(v_lakeEnv_7678_, 1);
if (v_linkDeps_7672_ == 0)
{
lean_object* v___x_7692_; 
v___x_7692_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7681_ = v___x_7692_;
v___y_7682_ = v_a_7675_;
goto v___jp_7680_;
}
else
{
lean_object* v___x_7693_; 
v___x_7693_ = l_Lake_mkLinkOrder___redArg(v_libs_7670_, v_a_7675_);
if (lean_obj_tag(v___x_7693_) == 0)
{
lean_object* v_a_7694_; lean_object* v_a_7695_; 
v_a_7694_ = lean_ctor_get(v___x_7693_, 0);
lean_inc(v_a_7694_);
v_a_7695_ = lean_ctor_get(v___x_7693_, 1);
lean_inc(v_a_7695_);
lean_dec_ref_known(v___x_7693_, 2);
v_libs_7681_ = v_a_7694_;
v___y_7682_ = v_a_7695_;
goto v___jp_7680_;
}
else
{
lean_object* v_a_7696_; lean_object* v_a_7697_; lean_object* v___x_7699_; uint8_t v_isShared_7700_; uint8_t v_isSharedCheck_7704_; 
v_a_7696_ = lean_ctor_get(v___x_7693_, 0);
v_a_7697_ = lean_ctor_get(v___x_7693_, 1);
v_isSharedCheck_7704_ = !lean_is_exclusive(v___x_7693_);
if (v_isSharedCheck_7704_ == 0)
{
v___x_7699_ = v___x_7693_;
v_isShared_7700_ = v_isSharedCheck_7704_;
goto v_resetjp_7698_;
}
else
{
lean_inc(v_a_7697_);
lean_inc(v_a_7696_);
lean_dec(v___x_7693_);
v___x_7699_ = lean_box(0);
v_isShared_7700_ = v_isSharedCheck_7704_;
goto v_resetjp_7698_;
}
v_resetjp_7698_:
{
lean_object* v___x_7702_; 
if (v_isShared_7700_ == 0)
{
v___x_7702_ = v___x_7699_;
goto v_reusejp_7701_;
}
else
{
lean_object* v_reuseFailAlloc_7703_; 
v_reuseFailAlloc_7703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7703_, 0, v_a_7696_);
lean_ctor_set(v_reuseFailAlloc_7703_, 1, v_a_7697_);
v___x_7702_ = v_reuseFailAlloc_7703_;
goto v_reusejp_7701_;
}
v_reusejp_7701_:
{
return v___x_7702_;
}
}
}
}
v___jp_7680_:
{
lean_object* v_leanLibDir_7683_; lean_object* v___x_7684_; lean_object* v___x_7685_; lean_object* v___x_7686_; lean_object* v___x_7687_; lean_object* v___x_7688_; lean_object* v___x_7689_; lean_object* v___x_7690_; lean_object* v___x_7691_; 
v_leanLibDir_7683_ = lean_ctor_get(v_lean_7679_, 3);
v___x_7684_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7669_, v_libs_7681_);
lean_dec_ref(v_libs_7681_);
v___x_7685_ = l_Array_append___redArg(v___x_7684_, v_args_7671_);
v___x_7686_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7683_);
v___x_7687_ = lean_array_push(v___x_7686_, v_leanLibDir_7683_);
v___x_7688_ = l_Array_append___redArg(v___x_7685_, v___x_7687_);
lean_dec_ref(v___x_7687_);
v___x_7689_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7673_, v_lean_7679_);
v___x_7690_ = l_Array_append___redArg(v___x_7688_, v___x_7689_);
lean_dec_ref(v___x_7689_);
v___x_7691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7691_, 0, v___x_7690_);
lean_ctor_set(v___x_7691_, 1, v___y_7682_);
return v___x_7691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object* v_objs_7705_, lean_object* v_libs_7706_, lean_object* v_args_7707_, lean_object* v_linkDeps_7708_, lean_object* v_sharedLean_7709_, lean_object* v_a_7710_, lean_object* v_a_7711_, lean_object* v_a_7712_){
_start:
{
uint8_t v_linkDeps_boxed_7713_; uint8_t v_sharedLean_boxed_7714_; lean_object* v_res_7715_; 
v_linkDeps_boxed_7713_ = lean_unbox(v_linkDeps_7708_);
v_sharedLean_boxed_7714_ = lean_unbox(v_sharedLean_7709_);
v_res_7715_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(v_objs_7705_, v_libs_7706_, v_args_7707_, v_linkDeps_boxed_7713_, v_sharedLean_boxed_7714_, v_a_7710_, v_a_7711_);
lean_dec_ref(v_a_7710_);
lean_dec_ref(v_args_7707_);
lean_dec_ref(v_libs_7706_);
lean_dec_ref(v_objs_7705_);
return v_res_7715_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object* v_objs_7716_, lean_object* v_libs_7717_, lean_object* v_args_7718_, uint8_t v_linkDeps_7719_, uint8_t v_sharedLean_7720_, lean_object* v_a_7721_, lean_object* v_a_7722_, lean_object* v_a_7723_, lean_object* v_a_7724_, lean_object* v_a_7725_, lean_object* v_a_7726_){
_start:
{
lean_object* v_toContext_7728_; lean_object* v_lakeEnv_7729_; lean_object* v_lean_7730_; lean_object* v_libs_7732_; lean_object* v___y_7733_; 
v_toContext_7728_ = lean_ctor_get(v_a_7725_, 1);
v_lakeEnv_7729_ = lean_ctor_get(v_toContext_7728_, 0);
v_lean_7730_ = lean_ctor_get(v_lakeEnv_7729_, 1);
if (v_linkDeps_7719_ == 0)
{
lean_object* v___x_7745_; 
v___x_7745_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7732_ = v___x_7745_;
v___y_7733_ = v_a_7726_;
goto v___jp_7731_;
}
else
{
lean_object* v___x_7746_; 
v___x_7746_ = l_Lake_mkLinkOrder___redArg(v_libs_7717_, v_a_7726_);
if (lean_obj_tag(v___x_7746_) == 0)
{
lean_object* v_a_7747_; lean_object* v_a_7748_; 
v_a_7747_ = lean_ctor_get(v___x_7746_, 0);
lean_inc(v_a_7747_);
v_a_7748_ = lean_ctor_get(v___x_7746_, 1);
lean_inc(v_a_7748_);
lean_dec_ref_known(v___x_7746_, 2);
v_libs_7732_ = v_a_7747_;
v___y_7733_ = v_a_7748_;
goto v___jp_7731_;
}
else
{
lean_object* v_a_7749_; lean_object* v_a_7750_; lean_object* v___x_7752_; uint8_t v_isShared_7753_; uint8_t v_isSharedCheck_7757_; 
v_a_7749_ = lean_ctor_get(v___x_7746_, 0);
v_a_7750_ = lean_ctor_get(v___x_7746_, 1);
v_isSharedCheck_7757_ = !lean_is_exclusive(v___x_7746_);
if (v_isSharedCheck_7757_ == 0)
{
v___x_7752_ = v___x_7746_;
v_isShared_7753_ = v_isSharedCheck_7757_;
goto v_resetjp_7751_;
}
else
{
lean_inc(v_a_7750_);
lean_inc(v_a_7749_);
lean_dec(v___x_7746_);
v___x_7752_ = lean_box(0);
v_isShared_7753_ = v_isSharedCheck_7757_;
goto v_resetjp_7751_;
}
v_resetjp_7751_:
{
lean_object* v___x_7755_; 
if (v_isShared_7753_ == 0)
{
v___x_7755_ = v___x_7752_;
goto v_reusejp_7754_;
}
else
{
lean_object* v_reuseFailAlloc_7756_; 
v_reuseFailAlloc_7756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7756_, 0, v_a_7749_);
lean_ctor_set(v_reuseFailAlloc_7756_, 1, v_a_7750_);
v___x_7755_ = v_reuseFailAlloc_7756_;
goto v_reusejp_7754_;
}
v_reusejp_7754_:
{
return v___x_7755_;
}
}
}
}
v___jp_7731_:
{
lean_object* v_leanLibDir_7734_; lean_object* v___x_7735_; lean_object* v___x_7736_; lean_object* v___x_7737_; lean_object* v___x_7738_; lean_object* v___x_7739_; lean_object* v___x_7740_; lean_object* v___x_7741_; lean_object* v___x_7742_; lean_object* v___x_7743_; lean_object* v___x_7744_; 
v_leanLibDir_7734_ = lean_ctor_get(v_lean_7730_, 3);
v___x_7735_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7716_, v_libs_7732_);
lean_dec_ref(v_libs_7732_);
v___x_7736_ = l_Array_append___redArg(v___x_7735_, v_args_7718_);
v___x_7737_ = lean_unsigned_to_nat(2u);
v___x_7738_ = lean_mk_empty_array_with_capacity(v___x_7737_);
lean_dec_ref(v___x_7738_);
v___x_7739_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7734_);
v___x_7740_ = lean_array_push(v___x_7739_, v_leanLibDir_7734_);
v___x_7741_ = l_Array_append___redArg(v___x_7736_, v___x_7740_);
lean_dec_ref(v___x_7740_);
v___x_7742_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7720_, v_lean_7730_);
v___x_7743_ = l_Array_append___redArg(v___x_7741_, v___x_7742_);
lean_dec_ref(v___x_7742_);
v___x_7744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7744_, 0, v___x_7743_);
lean_ctor_set(v___x_7744_, 1, v___y_7733_);
return v___x_7744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object* v_objs_7758_, lean_object* v_libs_7759_, lean_object* v_args_7760_, lean_object* v_linkDeps_7761_, lean_object* v_sharedLean_7762_, lean_object* v_a_7763_, lean_object* v_a_7764_, lean_object* v_a_7765_, lean_object* v_a_7766_, lean_object* v_a_7767_, lean_object* v_a_7768_, lean_object* v_a_7769_){
_start:
{
uint8_t v_linkDeps_boxed_7770_; uint8_t v_sharedLean_boxed_7771_; lean_object* v_res_7772_; 
v_linkDeps_boxed_7770_ = lean_unbox(v_linkDeps_7761_);
v_sharedLean_boxed_7771_ = lean_unbox(v_sharedLean_7762_);
v_res_7772_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(v_objs_7758_, v_libs_7759_, v_args_7760_, v_linkDeps_boxed_7770_, v_sharedLean_boxed_7771_, v_a_7763_, v_a_7764_, v_a_7765_, v_a_7766_, v_a_7767_, v_a_7768_);
lean_dec_ref(v_a_7767_);
lean_dec(v_a_7766_);
lean_dec(v_a_7765_);
lean_dec(v_a_7764_);
lean_dec_ref(v_a_7763_);
lean_dec_ref(v_args_7760_);
lean_dec_ref(v_libs_7759_);
lean_dec_ref(v_objs_7758_);
return v_res_7772_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object* v_linkObjs_7773_, lean_object* v_args_7774_, lean_object* v_libFile_7775_, lean_object* v_linker_7776_, uint8_t v_linkDeps_7777_, lean_object* v_linkLibs_7778_, lean_object* v___y_7779_, lean_object* v___y_7780_, lean_object* v___y_7781_, lean_object* v___y_7782_, lean_object* v___y_7783_, lean_object* v___y_7784_){
_start:
{
lean_object* v_libs_7787_; lean_object* v___y_7788_; 
if (v_linkDeps_7777_ == 0)
{
lean_object* v___x_7825_; 
v___x_7825_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7787_ = v___x_7825_;
v___y_7788_ = v___y_7784_;
goto v___jp_7786_;
}
else
{
lean_object* v___x_7826_; 
v___x_7826_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_7778_, v___y_7784_);
if (lean_obj_tag(v___x_7826_) == 0)
{
lean_object* v_a_7827_; lean_object* v_a_7828_; 
v_a_7827_ = lean_ctor_get(v___x_7826_, 0);
lean_inc(v_a_7827_);
v_a_7828_ = lean_ctor_get(v___x_7826_, 1);
lean_inc(v_a_7828_);
lean_dec_ref_known(v___x_7826_, 2);
v_libs_7787_ = v_a_7827_;
v___y_7788_ = v_a_7828_;
goto v___jp_7786_;
}
else
{
lean_object* v_a_7829_; lean_object* v_a_7830_; lean_object* v___x_7832_; uint8_t v_isShared_7833_; uint8_t v_isSharedCheck_7837_; 
lean_dec_ref(v_linker_7776_);
lean_dec_ref(v_libFile_7775_);
v_a_7829_ = lean_ctor_get(v___x_7826_, 0);
v_a_7830_ = lean_ctor_get(v___x_7826_, 1);
v_isSharedCheck_7837_ = !lean_is_exclusive(v___x_7826_);
if (v_isSharedCheck_7837_ == 0)
{
v___x_7832_ = v___x_7826_;
v_isShared_7833_ = v_isSharedCheck_7837_;
goto v_resetjp_7831_;
}
else
{
lean_inc(v_a_7830_);
lean_inc(v_a_7829_);
lean_dec(v___x_7826_);
v___x_7832_ = lean_box(0);
v_isShared_7833_ = v_isSharedCheck_7837_;
goto v_resetjp_7831_;
}
v_resetjp_7831_:
{
lean_object* v___x_7835_; 
if (v_isShared_7833_ == 0)
{
v___x_7835_ = v___x_7832_;
goto v_reusejp_7834_;
}
else
{
lean_object* v_reuseFailAlloc_7836_; 
v_reuseFailAlloc_7836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7836_, 0, v_a_7829_);
lean_ctor_set(v_reuseFailAlloc_7836_, 1, v_a_7830_);
v___x_7835_ = v_reuseFailAlloc_7836_;
goto v_reusejp_7834_;
}
v_reusejp_7834_:
{
return v___x_7835_;
}
}
}
}
v___jp_7786_:
{
lean_object* v_log_7789_; uint8_t v_action_7790_; uint8_t v_wantsRebuild_7791_; lean_object* v_trace_7792_; lean_object* v_buildTime_7793_; lean_object* v___x_7795_; uint8_t v_isShared_7796_; uint8_t v_isSharedCheck_7824_; 
v_log_7789_ = lean_ctor_get(v___y_7788_, 0);
v_action_7790_ = lean_ctor_get_uint8(v___y_7788_, sizeof(void*)*3);
v_wantsRebuild_7791_ = lean_ctor_get_uint8(v___y_7788_, sizeof(void*)*3 + 1);
v_trace_7792_ = lean_ctor_get(v___y_7788_, 1);
v_buildTime_7793_ = lean_ctor_get(v___y_7788_, 2);
v_isSharedCheck_7824_ = !lean_is_exclusive(v___y_7788_);
if (v_isSharedCheck_7824_ == 0)
{
v___x_7795_ = v___y_7788_;
v_isShared_7796_ = v_isSharedCheck_7824_;
goto v_resetjp_7794_;
}
else
{
lean_inc(v_buildTime_7793_);
lean_inc(v_trace_7792_);
lean_inc(v_log_7789_);
lean_dec(v___y_7788_);
v___x_7795_ = lean_box(0);
v_isShared_7796_ = v_isSharedCheck_7824_;
goto v_resetjp_7794_;
}
v_resetjp_7794_:
{
lean_object* v___x_7797_; lean_object* v___x_7798_; lean_object* v___x_7799_; 
v___x_7797_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_7773_, v_libs_7787_);
lean_dec_ref(v_libs_7787_);
v___x_7798_ = l_Array_append___redArg(v___x_7797_, v_args_7774_);
v___x_7799_ = l_Lake_compileSharedLib(v_libFile_7775_, v___x_7798_, v_linker_7776_, v_log_7789_);
lean_dec_ref(v___x_7798_);
if (lean_obj_tag(v___x_7799_) == 0)
{
lean_object* v_a_7800_; lean_object* v_a_7801_; lean_object* v___x_7803_; uint8_t v_isShared_7804_; uint8_t v_isSharedCheck_7811_; 
v_a_7800_ = lean_ctor_get(v___x_7799_, 0);
v_a_7801_ = lean_ctor_get(v___x_7799_, 1);
v_isSharedCheck_7811_ = !lean_is_exclusive(v___x_7799_);
if (v_isSharedCheck_7811_ == 0)
{
v___x_7803_ = v___x_7799_;
v_isShared_7804_ = v_isSharedCheck_7811_;
goto v_resetjp_7802_;
}
else
{
lean_inc(v_a_7801_);
lean_inc(v_a_7800_);
lean_dec(v___x_7799_);
v___x_7803_ = lean_box(0);
v_isShared_7804_ = v_isSharedCheck_7811_;
goto v_resetjp_7802_;
}
v_resetjp_7802_:
{
lean_object* v___x_7806_; 
if (v_isShared_7796_ == 0)
{
lean_ctor_set(v___x_7795_, 0, v_a_7801_);
v___x_7806_ = v___x_7795_;
goto v_reusejp_7805_;
}
else
{
lean_object* v_reuseFailAlloc_7810_; 
v_reuseFailAlloc_7810_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7810_, 0, v_a_7801_);
lean_ctor_set(v_reuseFailAlloc_7810_, 1, v_trace_7792_);
lean_ctor_set(v_reuseFailAlloc_7810_, 2, v_buildTime_7793_);
lean_ctor_set_uint8(v_reuseFailAlloc_7810_, sizeof(void*)*3, v_action_7790_);
lean_ctor_set_uint8(v_reuseFailAlloc_7810_, sizeof(void*)*3 + 1, v_wantsRebuild_7791_);
v___x_7806_ = v_reuseFailAlloc_7810_;
goto v_reusejp_7805_;
}
v_reusejp_7805_:
{
lean_object* v___x_7808_; 
if (v_isShared_7804_ == 0)
{
lean_ctor_set(v___x_7803_, 1, v___x_7806_);
v___x_7808_ = v___x_7803_;
goto v_reusejp_7807_;
}
else
{
lean_object* v_reuseFailAlloc_7809_; 
v_reuseFailAlloc_7809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7809_, 0, v_a_7800_);
lean_ctor_set(v_reuseFailAlloc_7809_, 1, v___x_7806_);
v___x_7808_ = v_reuseFailAlloc_7809_;
goto v_reusejp_7807_;
}
v_reusejp_7807_:
{
return v___x_7808_;
}
}
}
}
else
{
lean_object* v_a_7812_; lean_object* v_a_7813_; lean_object* v___x_7815_; uint8_t v_isShared_7816_; uint8_t v_isSharedCheck_7823_; 
v_a_7812_ = lean_ctor_get(v___x_7799_, 0);
v_a_7813_ = lean_ctor_get(v___x_7799_, 1);
v_isSharedCheck_7823_ = !lean_is_exclusive(v___x_7799_);
if (v_isSharedCheck_7823_ == 0)
{
v___x_7815_ = v___x_7799_;
v_isShared_7816_ = v_isSharedCheck_7823_;
goto v_resetjp_7814_;
}
else
{
lean_inc(v_a_7813_);
lean_inc(v_a_7812_);
lean_dec(v___x_7799_);
v___x_7815_ = lean_box(0);
v_isShared_7816_ = v_isSharedCheck_7823_;
goto v_resetjp_7814_;
}
v_resetjp_7814_:
{
lean_object* v___x_7818_; 
if (v_isShared_7796_ == 0)
{
lean_ctor_set(v___x_7795_, 0, v_a_7813_);
v___x_7818_ = v___x_7795_;
goto v_reusejp_7817_;
}
else
{
lean_object* v_reuseFailAlloc_7822_; 
v_reuseFailAlloc_7822_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7822_, 0, v_a_7813_);
lean_ctor_set(v_reuseFailAlloc_7822_, 1, v_trace_7792_);
lean_ctor_set(v_reuseFailAlloc_7822_, 2, v_buildTime_7793_);
lean_ctor_set_uint8(v_reuseFailAlloc_7822_, sizeof(void*)*3, v_action_7790_);
lean_ctor_set_uint8(v_reuseFailAlloc_7822_, sizeof(void*)*3 + 1, v_wantsRebuild_7791_);
v___x_7818_ = v_reuseFailAlloc_7822_;
goto v_reusejp_7817_;
}
v_reusejp_7817_:
{
lean_object* v___x_7820_; 
if (v_isShared_7816_ == 0)
{
lean_ctor_set(v___x_7815_, 1, v___x_7818_);
v___x_7820_ = v___x_7815_;
goto v_reusejp_7819_;
}
else
{
lean_object* v_reuseFailAlloc_7821_; 
v_reuseFailAlloc_7821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7821_, 0, v_a_7812_);
lean_ctor_set(v_reuseFailAlloc_7821_, 1, v___x_7818_);
v___x_7820_ = v_reuseFailAlloc_7821_;
goto v_reusejp_7819_;
}
v_reusejp_7819_:
{
return v___x_7820_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_7838_, lean_object* v_args_7839_, lean_object* v_libFile_7840_, lean_object* v_linker_7841_, lean_object* v_linkDeps_7842_, lean_object* v_linkLibs_7843_, lean_object* v___y_7844_, lean_object* v___y_7845_, lean_object* v___y_7846_, lean_object* v___y_7847_, lean_object* v___y_7848_, lean_object* v___y_7849_, lean_object* v___y_7850_){
_start:
{
uint8_t v_linkDeps_boxed_7851_; lean_object* v_res_7852_; 
v_linkDeps_boxed_7851_ = lean_unbox(v_linkDeps_7842_);
v_res_7852_ = l_Lake_buildSharedLibSync___lam__0(v_linkObjs_7838_, v_args_7839_, v_libFile_7840_, v_linker_7841_, v_linkDeps_boxed_7851_, v_linkLibs_7843_, v___y_7844_, v___y_7845_, v___y_7846_, v___y_7847_, v___y_7848_, v___y_7849_);
lean_dec_ref(v___y_7848_);
lean_dec(v___y_7847_);
lean_dec(v___y_7846_);
lean_dec(v___y_7845_);
lean_dec_ref(v___y_7844_);
lean_dec_ref(v_linkLibs_7843_);
lean_dec_ref(v_args_7839_);
lean_dec_ref(v_linkObjs_7838_);
return v_res_7852_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object* v_libName_7853_, lean_object* v_libFile_7854_, lean_object* v_linkObjs_7855_, lean_object* v_linkLibs_7856_, lean_object* v_args_7857_, lean_object* v_linker_7858_, uint8_t v_plugin_7859_, uint8_t v_linkDeps_7860_, lean_object* v_a_7861_, lean_object* v_a_7862_, lean_object* v_a_7863_, lean_object* v_a_7864_, lean_object* v_a_7865_, lean_object* v_a_7866_){
_start:
{
lean_object* v_log_7868_; uint8_t v_action_7869_; uint8_t v_wantsRebuild_7870_; lean_object* v_trace_7871_; lean_object* v_buildTime_7872_; lean_object* v___x_7874_; uint8_t v_isShared_7875_; uint8_t v_isSharedCheck_7908_; 
v_log_7868_ = lean_ctor_get(v_a_7866_, 0);
v_action_7869_ = lean_ctor_get_uint8(v_a_7866_, sizeof(void*)*3);
v_wantsRebuild_7870_ = lean_ctor_get_uint8(v_a_7866_, sizeof(void*)*3 + 1);
v_trace_7871_ = lean_ctor_get(v_a_7866_, 1);
v_buildTime_7872_ = lean_ctor_get(v_a_7866_, 2);
v_isSharedCheck_7908_ = !lean_is_exclusive(v_a_7866_);
if (v_isSharedCheck_7908_ == 0)
{
v___x_7874_ = v_a_7866_;
v_isShared_7875_ = v_isSharedCheck_7908_;
goto v_resetjp_7873_;
}
else
{
lean_inc(v_buildTime_7872_);
lean_inc(v_trace_7871_);
lean_inc(v_log_7868_);
lean_dec(v_a_7866_);
v___x_7874_ = lean_box(0);
v_isShared_7875_ = v_isSharedCheck_7908_;
goto v_resetjp_7873_;
}
v_resetjp_7873_:
{
lean_object* v___x_7876_; lean_object* v___f_7877_; lean_object* v___x_7878_; lean_object* v___x_7879_; lean_object* v___x_7881_; 
v___x_7876_ = lean_box(v_linkDeps_7860_);
lean_inc_ref(v_linkLibs_7856_);
lean_inc_ref(v_libFile_7854_);
v___f_7877_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7877_, 0, v_linkObjs_7855_);
lean_closure_set(v___f_7877_, 1, v_args_7857_);
lean_closure_set(v___f_7877_, 2, v_libFile_7854_);
lean_closure_set(v___f_7877_, 3, v_linker_7858_);
lean_closure_set(v___f_7877_, 4, v___x_7876_);
lean_closure_set(v___f_7877_, 5, v_linkLibs_7856_);
v___x_7878_ = l_Lake_platformTrace;
v___x_7879_ = l_Lake_BuildTrace_mix(v_trace_7871_, v___x_7878_);
if (v_isShared_7875_ == 0)
{
lean_ctor_set(v___x_7874_, 1, v___x_7879_);
v___x_7881_ = v___x_7874_;
goto v_reusejp_7880_;
}
else
{
lean_object* v_reuseFailAlloc_7907_; 
v_reuseFailAlloc_7907_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7907_, 0, v_log_7868_);
lean_ctor_set(v_reuseFailAlloc_7907_, 1, v___x_7879_);
lean_ctor_set(v_reuseFailAlloc_7907_, 2, v_buildTime_7872_);
lean_ctor_set_uint8(v_reuseFailAlloc_7907_, sizeof(void*)*3, v_action_7869_);
lean_ctor_set_uint8(v_reuseFailAlloc_7907_, sizeof(void*)*3 + 1, v_wantsRebuild_7870_);
v___x_7881_ = v_reuseFailAlloc_7907_;
goto v_reusejp_7880_;
}
v_reusejp_7880_:
{
uint8_t v___x_7882_; lean_object* v___x_7883_; uint8_t v___x_7884_; lean_object* v___x_7885_; 
v___x_7882_ = 0;
v___x_7883_ = l_Lake_sharedLibExt;
v___x_7884_ = 1;
v___x_7885_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7854_, v___f_7877_, v___x_7882_, v___x_7883_, v___x_7884_, v___x_7882_, v___x_7882_, v_a_7861_, v_a_7862_, v_a_7863_, v_a_7864_, v_a_7865_, v___x_7881_);
if (lean_obj_tag(v___x_7885_) == 0)
{
lean_object* v_a_7886_; lean_object* v_a_7887_; lean_object* v___x_7889_; uint8_t v_isShared_7890_; uint8_t v_isSharedCheck_7897_; 
v_a_7886_ = lean_ctor_get(v___x_7885_, 0);
v_a_7887_ = lean_ctor_get(v___x_7885_, 1);
v_isSharedCheck_7897_ = !lean_is_exclusive(v___x_7885_);
if (v_isSharedCheck_7897_ == 0)
{
v___x_7889_ = v___x_7885_;
v_isShared_7890_ = v_isSharedCheck_7897_;
goto v_resetjp_7888_;
}
else
{
lean_inc(v_a_7887_);
lean_inc(v_a_7886_);
lean_dec(v___x_7885_);
v___x_7889_ = lean_box(0);
v_isShared_7890_ = v_isSharedCheck_7897_;
goto v_resetjp_7888_;
}
v_resetjp_7888_:
{
lean_object* v_path_7891_; lean_object* v___x_7892_; lean_object* v___x_7893_; lean_object* v___x_7895_; 
v_path_7891_ = lean_ctor_get(v_a_7886_, 1);
lean_inc_ref(v_path_7891_);
lean_dec(v_a_7886_);
v___x_7892_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7893_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_7893_, 0, v_path_7891_);
lean_ctor_set(v___x_7893_, 1, v_libName_7853_);
lean_ctor_set(v___x_7893_, 2, v_linkLibs_7856_);
lean_ctor_set(v___x_7893_, 3, v___x_7892_);
lean_ctor_set_uint8(v___x_7893_, sizeof(void*)*4, v_plugin_7859_);
if (v_isShared_7890_ == 0)
{
lean_ctor_set(v___x_7889_, 0, v___x_7893_);
v___x_7895_ = v___x_7889_;
goto v_reusejp_7894_;
}
else
{
lean_object* v_reuseFailAlloc_7896_; 
v_reuseFailAlloc_7896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7896_, 0, v___x_7893_);
lean_ctor_set(v_reuseFailAlloc_7896_, 1, v_a_7887_);
v___x_7895_ = v_reuseFailAlloc_7896_;
goto v_reusejp_7894_;
}
v_reusejp_7894_:
{
return v___x_7895_;
}
}
}
else
{
lean_object* v_a_7898_; lean_object* v_a_7899_; lean_object* v___x_7901_; uint8_t v_isShared_7902_; uint8_t v_isSharedCheck_7906_; 
lean_dec_ref(v_linkLibs_7856_);
lean_dec_ref(v_libName_7853_);
v_a_7898_ = lean_ctor_get(v___x_7885_, 0);
v_a_7899_ = lean_ctor_get(v___x_7885_, 1);
v_isSharedCheck_7906_ = !lean_is_exclusive(v___x_7885_);
if (v_isSharedCheck_7906_ == 0)
{
v___x_7901_ = v___x_7885_;
v_isShared_7902_ = v_isSharedCheck_7906_;
goto v_resetjp_7900_;
}
else
{
lean_inc(v_a_7899_);
lean_inc(v_a_7898_);
lean_dec(v___x_7885_);
v___x_7901_ = lean_box(0);
v_isShared_7902_ = v_isSharedCheck_7906_;
goto v_resetjp_7900_;
}
v_resetjp_7900_:
{
lean_object* v___x_7904_; 
if (v_isShared_7902_ == 0)
{
v___x_7904_ = v___x_7901_;
goto v_reusejp_7903_;
}
else
{
lean_object* v_reuseFailAlloc_7905_; 
v_reuseFailAlloc_7905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7905_, 0, v_a_7898_);
lean_ctor_set(v_reuseFailAlloc_7905_, 1, v_a_7899_);
v___x_7904_ = v_reuseFailAlloc_7905_;
goto v_reusejp_7903_;
}
v_reusejp_7903_:
{
return v___x_7904_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object* v_libName_7909_, lean_object* v_libFile_7910_, lean_object* v_linkObjs_7911_, lean_object* v_linkLibs_7912_, lean_object* v_args_7913_, lean_object* v_linker_7914_, lean_object* v_plugin_7915_, lean_object* v_linkDeps_7916_, lean_object* v_a_7917_, lean_object* v_a_7918_, lean_object* v_a_7919_, lean_object* v_a_7920_, lean_object* v_a_7921_, lean_object* v_a_7922_, lean_object* v_a_7923_){
_start:
{
uint8_t v_plugin_boxed_7924_; uint8_t v_linkDeps_boxed_7925_; lean_object* v_res_7926_; 
v_plugin_boxed_7924_ = lean_unbox(v_plugin_7915_);
v_linkDeps_boxed_7925_ = lean_unbox(v_linkDeps_7916_);
v_res_7926_ = l_Lake_buildSharedLibSync(v_libName_7909_, v_libFile_7910_, v_linkObjs_7911_, v_linkLibs_7912_, v_args_7913_, v_linker_7914_, v_plugin_boxed_7924_, v_linkDeps_boxed_7925_, v_a_7917_, v_a_7918_, v_a_7919_, v_a_7920_, v_a_7921_, v_a_7922_);
lean_dec_ref(v_a_7921_);
lean_dec(v_a_7920_);
lean_dec(v_a_7919_);
lean_dec(v_a_7918_);
return v_res_7926_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_extraDepTrace_7927_, lean_object* v_traceArgs_7928_, lean_object* v_weakArgs_7929_, lean_object* v_libName_7930_, lean_object* v_libFile_7931_, lean_object* v_objs_7932_, lean_object* v_linker_7933_, uint8_t v_plugin_7934_, uint8_t v_linkDeps_7935_, lean_object* v_libs_7936_, lean_object* v___y_7937_, lean_object* v___y_7938_, lean_object* v___y_7939_, lean_object* v___y_7940_, lean_object* v___y_7941_, lean_object* v___y_7942_){
_start:
{
lean_object* v___x_7944_; 
lean_inc_ref(v___y_7941_);
lean_inc(v___y_7940_);
lean_inc(v___y_7939_);
lean_inc(v___y_7938_);
lean_inc_ref(v___y_7937_);
v___x_7944_ = lean_apply_7(v_extraDepTrace_7927_, v___y_7937_, v___y_7938_, v___y_7939_, v___y_7940_, v___y_7941_, v___y_7942_, lean_box(0));
if (lean_obj_tag(v___x_7944_) == 0)
{
lean_object* v_a_7945_; lean_object* v_a_7946_; lean_object* v_log_7947_; uint8_t v_action_7948_; uint8_t v_wantsRebuild_7949_; lean_object* v_trace_7950_; lean_object* v_buildTime_7951_; lean_object* v___x_7953_; uint8_t v_isShared_7954_; uint8_t v_isSharedCheck_7984_; 
v_a_7945_ = lean_ctor_get(v___x_7944_, 1);
lean_inc(v_a_7945_);
v_a_7946_ = lean_ctor_get(v___x_7944_, 0);
lean_inc(v_a_7946_);
lean_dec_ref_known(v___x_7944_, 2);
v_log_7947_ = lean_ctor_get(v_a_7945_, 0);
v_action_7948_ = lean_ctor_get_uint8(v_a_7945_, sizeof(void*)*3);
v_wantsRebuild_7949_ = lean_ctor_get_uint8(v_a_7945_, sizeof(void*)*3 + 1);
v_trace_7950_ = lean_ctor_get(v_a_7945_, 1);
v_buildTime_7951_ = lean_ctor_get(v_a_7945_, 2);
v_isSharedCheck_7984_ = !lean_is_exclusive(v_a_7945_);
if (v_isSharedCheck_7984_ == 0)
{
v___x_7953_ = v_a_7945_;
v_isShared_7954_ = v_isSharedCheck_7984_;
goto v_resetjp_7952_;
}
else
{
lean_inc(v_buildTime_7951_);
lean_inc(v_trace_7950_);
lean_inc(v_log_7947_);
lean_dec(v_a_7945_);
v___x_7953_ = lean_box(0);
v_isShared_7954_ = v_isSharedCheck_7984_;
goto v_resetjp_7952_;
}
v_resetjp_7952_:
{
lean_object* v___x_7955_; uint64_t v___y_7957_; uint64_t v___x_7973_; lean_object* v___x_7974_; lean_object* v___x_7975_; uint8_t v___x_7976_; 
v___x_7955_ = l_Lake_BuildTrace_mix(v_trace_7950_, v_a_7946_);
v___x_7973_ = l_Lake_Hash_nil;
v___x_7974_ = lean_unsigned_to_nat(0u);
v___x_7975_ = lean_array_get_size(v_traceArgs_7928_);
v___x_7976_ = lean_nat_dec_lt(v___x_7974_, v___x_7975_);
if (v___x_7976_ == 0)
{
v___y_7957_ = v___x_7973_;
goto v___jp_7956_;
}
else
{
uint8_t v___x_7977_; 
v___x_7977_ = lean_nat_dec_le(v___x_7975_, v___x_7975_);
if (v___x_7977_ == 0)
{
if (v___x_7976_ == 0)
{
v___y_7957_ = v___x_7973_;
goto v___jp_7956_;
}
else
{
size_t v___x_7978_; size_t v___x_7979_; uint64_t v___x_7980_; 
v___x_7978_ = ((size_t)0ULL);
v___x_7979_ = lean_usize_of_nat(v___x_7975_);
v___x_7980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7928_, v___x_7978_, v___x_7979_, v___x_7973_);
v___y_7957_ = v___x_7980_;
goto v___jp_7956_;
}
}
else
{
size_t v___x_7981_; size_t v___x_7982_; uint64_t v___x_7983_; 
v___x_7981_ = ((size_t)0ULL);
v___x_7982_ = lean_usize_of_nat(v___x_7975_);
v___x_7983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7928_, v___x_7981_, v___x_7982_, v___x_7973_);
v___y_7957_ = v___x_7983_;
goto v___jp_7956_;
}
}
v___jp_7956_:
{
lean_object* v___x_7958_; lean_object* v___x_7959_; lean_object* v___x_7960_; lean_object* v___x_7961_; lean_object* v___x_7962_; lean_object* v___x_7963_; lean_object* v___x_7964_; lean_object* v___x_7965_; lean_object* v___x_7966_; lean_object* v___x_7967_; lean_object* v___x_7969_; 
v___x_7958_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7959_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_7928_);
v___x_7960_ = lean_array_to_list(v_traceArgs_7928_);
v___x_7961_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7960_);
lean_dec(v___x_7960_);
v___x_7962_ = lean_string_append(v___x_7959_, v___x_7961_);
lean_dec_ref(v___x_7961_);
v___x_7963_ = lean_string_append(v___x_7958_, v___x_7962_);
lean_dec_ref(v___x_7962_);
v___x_7964_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7965_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7966_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7966_, 0, v___x_7963_);
lean_ctor_set(v___x_7966_, 1, v___x_7964_);
lean_ctor_set(v___x_7966_, 2, v___x_7965_);
lean_ctor_set_uint64(v___x_7966_, sizeof(void*)*3, v___y_7957_);
v___x_7967_ = l_Lake_BuildTrace_mix(v___x_7955_, v___x_7966_);
if (v_isShared_7954_ == 0)
{
lean_ctor_set(v___x_7953_, 1, v___x_7967_);
v___x_7969_ = v___x_7953_;
goto v_reusejp_7968_;
}
else
{
lean_object* v_reuseFailAlloc_7972_; 
v_reuseFailAlloc_7972_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7972_, 0, v_log_7947_);
lean_ctor_set(v_reuseFailAlloc_7972_, 1, v___x_7967_);
lean_ctor_set(v_reuseFailAlloc_7972_, 2, v_buildTime_7951_);
lean_ctor_set_uint8(v_reuseFailAlloc_7972_, sizeof(void*)*3, v_action_7948_);
lean_ctor_set_uint8(v_reuseFailAlloc_7972_, sizeof(void*)*3 + 1, v_wantsRebuild_7949_);
v___x_7969_ = v_reuseFailAlloc_7972_;
goto v_reusejp_7968_;
}
v_reusejp_7968_:
{
lean_object* v___x_7970_; lean_object* v___x_7971_; 
v___x_7970_ = l_Array_append___redArg(v_weakArgs_7929_, v_traceArgs_7928_);
lean_dec_ref(v_traceArgs_7928_);
v___x_7971_ = l_Lake_buildSharedLibSync(v_libName_7930_, v_libFile_7931_, v_objs_7932_, v_libs_7936_, v___x_7970_, v_linker_7933_, v_plugin_7934_, v_linkDeps_7935_, v___y_7937_, v___y_7938_, v___y_7939_, v___y_7940_, v___y_7941_, v___x_7969_);
return v___x_7971_;
}
}
}
}
else
{
lean_object* v_a_7985_; lean_object* v_a_7986_; lean_object* v___x_7988_; uint8_t v_isShared_7989_; uint8_t v_isSharedCheck_7993_; 
lean_dec_ref(v___y_7937_);
lean_dec_ref(v_libs_7936_);
lean_dec_ref(v_linker_7933_);
lean_dec_ref(v_objs_7932_);
lean_dec_ref(v_libFile_7931_);
lean_dec_ref(v_libName_7930_);
lean_dec_ref(v_weakArgs_7929_);
lean_dec_ref(v_traceArgs_7928_);
v_a_7985_ = lean_ctor_get(v___x_7944_, 0);
v_a_7986_ = lean_ctor_get(v___x_7944_, 1);
v_isSharedCheck_7993_ = !lean_is_exclusive(v___x_7944_);
if (v_isSharedCheck_7993_ == 0)
{
v___x_7988_ = v___x_7944_;
v_isShared_7989_ = v_isSharedCheck_7993_;
goto v_resetjp_7987_;
}
else
{
lean_inc(v_a_7986_);
lean_inc(v_a_7985_);
lean_dec(v___x_7944_);
v___x_7988_ = lean_box(0);
v_isShared_7989_ = v_isSharedCheck_7993_;
goto v_resetjp_7987_;
}
v_resetjp_7987_:
{
lean_object* v___x_7991_; 
if (v_isShared_7989_ == 0)
{
v___x_7991_ = v___x_7988_;
goto v_reusejp_7990_;
}
else
{
lean_object* v_reuseFailAlloc_7992_; 
v_reuseFailAlloc_7992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7992_, 0, v_a_7985_);
lean_ctor_set(v_reuseFailAlloc_7992_, 1, v_a_7986_);
v___x_7991_ = v_reuseFailAlloc_7992_;
goto v_reusejp_7990_;
}
v_reusejp_7990_:
{
return v___x_7991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object** _args){
lean_object* v_extraDepTrace_7994_ = _args[0];
lean_object* v_traceArgs_7995_ = _args[1];
lean_object* v_weakArgs_7996_ = _args[2];
lean_object* v_libName_7997_ = _args[3];
lean_object* v_libFile_7998_ = _args[4];
lean_object* v_objs_7999_ = _args[5];
lean_object* v_linker_8000_ = _args[6];
lean_object* v_plugin_8001_ = _args[7];
lean_object* v_linkDeps_8002_ = _args[8];
lean_object* v_libs_8003_ = _args[9];
lean_object* v___y_8004_ = _args[10];
lean_object* v___y_8005_ = _args[11];
lean_object* v___y_8006_ = _args[12];
lean_object* v___y_8007_ = _args[13];
lean_object* v___y_8008_ = _args[14];
lean_object* v___y_8009_ = _args[15];
lean_object* v___y_8010_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8011_; uint8_t v_linkDeps_boxed_8012_; lean_object* v_res_8013_; 
v_plugin_boxed_8011_ = lean_unbox(v_plugin_8001_);
v_linkDeps_boxed_8012_ = lean_unbox(v_linkDeps_8002_);
v_res_8013_ = l_Lake_buildSharedLib___lam__0(v_extraDepTrace_7994_, v_traceArgs_7995_, v_weakArgs_7996_, v_libName_7997_, v_libFile_7998_, v_objs_7999_, v_linker_8000_, v_plugin_boxed_8011_, v_linkDeps_boxed_8012_, v_libs_8003_, v___y_8004_, v___y_8005_, v___y_8006_, v___y_8007_, v___y_8008_, v___y_8009_);
lean_dec_ref(v___y_8008_);
lean_dec(v___y_8007_);
lean_dec(v___y_8006_);
lean_dec(v___y_8005_);
return v_res_8013_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object* v_extraDepTrace_8015_, lean_object* v_traceArgs_8016_, lean_object* v_weakArgs_8017_, lean_object* v_libName_8018_, lean_object* v_libFile_8019_, lean_object* v_linker_8020_, uint8_t v_plugin_8021_, uint8_t v_linkDeps_8022_, lean_object* v_linkLibs_8023_, lean_object* v___x_8024_, lean_object* v_objs_8025_, lean_object* v___y_8026_, lean_object* v___y_8027_, lean_object* v___y_8028_, lean_object* v___y_8029_, lean_object* v___y_8030_, lean_object* v___y_8031_){
_start:
{
lean_object* v_trace_8033_; lean_object* v___x_8034_; lean_object* v___x_8035_; lean_object* v___f_8036_; lean_object* v___x_8037_; lean_object* v___x_8038_; lean_object* v___x_8039_; uint8_t v___x_8040_; lean_object* v___x_8041_; lean_object* v___x_8042_; 
v_trace_8033_ = lean_ctor_get(v___y_8031_, 1);
v___x_8034_ = lean_box(v_plugin_8021_);
v___x_8035_ = lean_box(v_linkDeps_8022_);
v___f_8036_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 17, 9);
lean_closure_set(v___f_8036_, 0, v_extraDepTrace_8015_);
lean_closure_set(v___f_8036_, 1, v_traceArgs_8016_);
lean_closure_set(v___f_8036_, 2, v_weakArgs_8017_);
lean_closure_set(v___f_8036_, 3, v_libName_8018_);
lean_closure_set(v___f_8036_, 4, v_libFile_8019_);
lean_closure_set(v___f_8036_, 5, v_objs_8025_);
lean_closure_set(v___f_8036_, 6, v_linker_8020_);
lean_closure_set(v___f_8036_, 7, v___x_8034_);
lean_closure_set(v___f_8036_, 8, v___x_8035_);
v___x_8037_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8038_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8023_, v___x_8037_);
v___x_8039_ = lean_unsigned_to_nat(0u);
v___x_8040_ = 0;
v___x_8041_ = l_Lake_Job_mapM___redArg(v___x_8024_, v___x_8038_, v___f_8036_, v___x_8039_, v___x_8040_, v___y_8026_, v___y_8027_, v___y_8028_, v___y_8029_, v___y_8030_, v_trace_8033_);
v___x_8042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8042_, 0, v___x_8041_);
lean_ctor_set(v___x_8042_, 1, v___y_8031_);
return v___x_8042_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8043_ = _args[0];
lean_object* v_traceArgs_8044_ = _args[1];
lean_object* v_weakArgs_8045_ = _args[2];
lean_object* v_libName_8046_ = _args[3];
lean_object* v_libFile_8047_ = _args[4];
lean_object* v_linker_8048_ = _args[5];
lean_object* v_plugin_8049_ = _args[6];
lean_object* v_linkDeps_8050_ = _args[7];
lean_object* v_linkLibs_8051_ = _args[8];
lean_object* v___x_8052_ = _args[9];
lean_object* v_objs_8053_ = _args[10];
lean_object* v___y_8054_ = _args[11];
lean_object* v___y_8055_ = _args[12];
lean_object* v___y_8056_ = _args[13];
lean_object* v___y_8057_ = _args[14];
lean_object* v___y_8058_ = _args[15];
lean_object* v___y_8059_ = _args[16];
lean_object* v___y_8060_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8061_; uint8_t v_linkDeps_boxed_8062_; lean_object* v_res_8063_; 
v_plugin_boxed_8061_ = lean_unbox(v_plugin_8049_);
v_linkDeps_boxed_8062_ = lean_unbox(v_linkDeps_8050_);
v_res_8063_ = l_Lake_buildSharedLib___lam__1(v_extraDepTrace_8043_, v_traceArgs_8044_, v_weakArgs_8045_, v_libName_8046_, v_libFile_8047_, v_linker_8048_, v_plugin_boxed_8061_, v_linkDeps_boxed_8062_, v_linkLibs_8051_, v___x_8052_, v_objs_8053_, v___y_8054_, v___y_8055_, v___y_8056_, v___y_8057_, v___y_8058_, v___y_8059_);
lean_dec_ref(v___y_8058_);
lean_dec(v___y_8057_);
lean_dec(v___y_8056_);
lean_dec(v___y_8055_);
lean_dec_ref(v_linkLibs_8051_);
return v_res_8063_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_8065_, lean_object* v_libFile_8066_, lean_object* v_linkObjs_8067_, lean_object* v_linkLibs_8068_, lean_object* v_weakArgs_8069_, lean_object* v_traceArgs_8070_, lean_object* v_linker_8071_, lean_object* v_extraDepTrace_8072_, uint8_t v_plugin_8073_, uint8_t v_linkDeps_8074_, lean_object* v_a_8075_, lean_object* v_a_8076_, lean_object* v_a_8077_, lean_object* v_a_8078_, lean_object* v_a_8079_, lean_object* v_a_8080_){
_start:
{
lean_object* v___x_8082_; lean_object* v___x_8083_; lean_object* v___x_8084_; lean_object* v___f_8085_; lean_object* v___x_8086_; lean_object* v___x_8087_; lean_object* v___x_8088_; uint8_t v___x_8089_; lean_object* v___x_8090_; 
v___x_8082_ = l_Lake_instDataKindDynlib;
v___x_8083_ = lean_box(v_plugin_8073_);
v___x_8084_ = lean_box(v_linkDeps_8074_);
v___f_8085_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 18, 10);
lean_closure_set(v___f_8085_, 0, v_extraDepTrace_8072_);
lean_closure_set(v___f_8085_, 1, v_traceArgs_8070_);
lean_closure_set(v___f_8085_, 2, v_weakArgs_8069_);
lean_closure_set(v___f_8085_, 3, v_libName_8065_);
lean_closure_set(v___f_8085_, 4, v_libFile_8066_);
lean_closure_set(v___f_8085_, 5, v_linker_8071_);
lean_closure_set(v___f_8085_, 6, v___x_8083_);
lean_closure_set(v___f_8085_, 7, v___x_8084_);
lean_closure_set(v___f_8085_, 8, v_linkLibs_8068_);
lean_closure_set(v___f_8085_, 9, v___x_8082_);
v___x_8086_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8087_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8067_, v___x_8086_);
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
lean_object* v_a_8101_ = _args[10];
lean_object* v_a_8102_ = _args[11];
lean_object* v_a_8103_ = _args[12];
lean_object* v_a_8104_ = _args[13];
lean_object* v_a_8105_ = _args[14];
lean_object* v_a_8106_ = _args[15];
lean_object* v_a_8107_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8108_; uint8_t v_linkDeps_boxed_8109_; lean_object* v_res_8110_; 
v_plugin_boxed_8108_ = lean_unbox(v_plugin_8099_);
v_linkDeps_boxed_8109_ = lean_unbox(v_linkDeps_8100_);
v_res_8110_ = l_Lake_buildSharedLib(v_libName_8091_, v_libFile_8092_, v_linkObjs_8093_, v_linkLibs_8094_, v_weakArgs_8095_, v_traceArgs_8096_, v_linker_8097_, v_extraDepTrace_8098_, v_plugin_boxed_8108_, v_linkDeps_boxed_8109_, v_a_8101_, v_a_8102_, v_a_8103_, v_a_8104_, v_a_8105_, v_a_8106_);
lean_dec_ref(v_a_8106_);
lean_dec_ref(v_a_8105_);
lean_dec(v_a_8104_);
lean_dec(v_a_8103_);
lean_dec(v_a_8102_);
lean_dec_ref(v_linkObjs_8093_);
return v_res_8110_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object* v_linkObjs_8111_, lean_object* v_args_8112_, uint8_t v___x_8113_, lean_object* v_libFile_8114_, uint8_t v_linkDeps_8115_, lean_object* v_linkLibs_8116_, lean_object* v___y_8117_, lean_object* v___y_8118_, lean_object* v___y_8119_, lean_object* v___y_8120_, lean_object* v___y_8121_, lean_object* v___y_8122_){
_start:
{
lean_object* v_toContext_8124_; lean_object* v_lakeEnv_8125_; lean_object* v_lean_8126_; lean_object* v_libs_8128_; lean_object* v___y_8129_; 
v_toContext_8124_ = lean_ctor_get(v___y_8121_, 1);
v_lakeEnv_8125_ = lean_ctor_get(v_toContext_8124_, 0);
v_lean_8126_ = lean_ctor_get(v_lakeEnv_8125_, 1);
if (v_linkDeps_8115_ == 0)
{
lean_object* v___x_8175_; 
v___x_8175_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_8128_ = v___x_8175_;
v___y_8129_ = v___y_8122_;
goto v___jp_8127_;
}
else
{
lean_object* v___x_8176_; 
v___x_8176_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8116_, v___y_8122_);
if (lean_obj_tag(v___x_8176_) == 0)
{
lean_object* v_a_8177_; lean_object* v_a_8178_; 
v_a_8177_ = lean_ctor_get(v___x_8176_, 0);
lean_inc(v_a_8177_);
v_a_8178_ = lean_ctor_get(v___x_8176_, 1);
lean_inc(v_a_8178_);
lean_dec_ref_known(v___x_8176_, 2);
v_libs_8128_ = v_a_8177_;
v___y_8129_ = v_a_8178_;
goto v___jp_8127_;
}
else
{
lean_object* v_a_8179_; lean_object* v_a_8180_; lean_object* v___x_8182_; uint8_t v_isShared_8183_; uint8_t v_isSharedCheck_8187_; 
lean_dec_ref(v_libFile_8114_);
v_a_8179_ = lean_ctor_get(v___x_8176_, 0);
v_a_8180_ = lean_ctor_get(v___x_8176_, 1);
v_isSharedCheck_8187_ = !lean_is_exclusive(v___x_8176_);
if (v_isSharedCheck_8187_ == 0)
{
v___x_8182_ = v___x_8176_;
v_isShared_8183_ = v_isSharedCheck_8187_;
goto v_resetjp_8181_;
}
else
{
lean_inc(v_a_8180_);
lean_inc(v_a_8179_);
lean_dec(v___x_8176_);
v___x_8182_ = lean_box(0);
v_isShared_8183_ = v_isSharedCheck_8187_;
goto v_resetjp_8181_;
}
v_resetjp_8181_:
{
lean_object* v___x_8185_; 
if (v_isShared_8183_ == 0)
{
v___x_8185_ = v___x_8182_;
goto v_reusejp_8184_;
}
else
{
lean_object* v_reuseFailAlloc_8186_; 
v_reuseFailAlloc_8186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8186_, 0, v_a_8179_);
lean_ctor_set(v_reuseFailAlloc_8186_, 1, v_a_8180_);
v___x_8185_ = v_reuseFailAlloc_8186_;
goto v_reusejp_8184_;
}
v_reusejp_8184_:
{
return v___x_8185_;
}
}
}
}
v___jp_8127_:
{
lean_object* v_leanLibDir_8130_; lean_object* v_cc_8131_; lean_object* v_log_8132_; uint8_t v_action_8133_; uint8_t v_wantsRebuild_8134_; lean_object* v_trace_8135_; lean_object* v_buildTime_8136_; lean_object* v___x_8138_; uint8_t v_isShared_8139_; uint8_t v_isSharedCheck_8174_; 
v_leanLibDir_8130_ = lean_ctor_get(v_lean_8126_, 3);
v_cc_8131_ = lean_ctor_get(v_lean_8126_, 14);
v_log_8132_ = lean_ctor_get(v___y_8129_, 0);
v_action_8133_ = lean_ctor_get_uint8(v___y_8129_, sizeof(void*)*3);
v_wantsRebuild_8134_ = lean_ctor_get_uint8(v___y_8129_, sizeof(void*)*3 + 1);
v_trace_8135_ = lean_ctor_get(v___y_8129_, 1);
v_buildTime_8136_ = lean_ctor_get(v___y_8129_, 2);
v_isSharedCheck_8174_ = !lean_is_exclusive(v___y_8129_);
if (v_isSharedCheck_8174_ == 0)
{
v___x_8138_ = v___y_8129_;
v_isShared_8139_ = v_isSharedCheck_8174_;
goto v_resetjp_8137_;
}
else
{
lean_inc(v_buildTime_8136_);
lean_inc(v_trace_8135_);
lean_inc(v_log_8132_);
lean_dec(v___y_8129_);
v___x_8138_ = lean_box(0);
v_isShared_8139_ = v_isSharedCheck_8174_;
goto v_resetjp_8137_;
}
v_resetjp_8137_:
{
lean_object* v___x_8140_; lean_object* v___x_8141_; lean_object* v___x_8142_; lean_object* v___x_8143_; lean_object* v___x_8144_; lean_object* v___x_8145_; lean_object* v___x_8146_; lean_object* v___x_8147_; lean_object* v___x_8148_; lean_object* v___x_8149_; 
v___x_8140_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8111_, v_libs_8128_);
lean_dec_ref(v_libs_8128_);
v___x_8141_ = l_Array_append___redArg(v___x_8140_, v_args_8112_);
v___x_8142_ = lean_unsigned_to_nat(2u);
v___x_8143_ = lean_mk_empty_array_with_capacity(v___x_8142_);
lean_dec_ref(v___x_8143_);
v___x_8144_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8130_);
v___x_8145_ = lean_array_push(v___x_8144_, v_leanLibDir_8130_);
v___x_8146_ = l_Array_append___redArg(v___x_8141_, v___x_8145_);
lean_dec_ref(v___x_8145_);
v___x_8147_ = l_Lake_LeanInstall_ccLinkFlags(v___x_8113_, v_lean_8126_);
v___x_8148_ = l_Array_append___redArg(v___x_8146_, v___x_8147_);
lean_dec_ref(v___x_8147_);
lean_inc_ref(v_cc_8131_);
v___x_8149_ = l_Lake_compileSharedLib(v_libFile_8114_, v___x_8148_, v_cc_8131_, v_log_8132_);
lean_dec_ref(v___x_8148_);
if (lean_obj_tag(v___x_8149_) == 0)
{
lean_object* v_a_8150_; lean_object* v_a_8151_; lean_object* v___x_8153_; uint8_t v_isShared_8154_; uint8_t v_isSharedCheck_8161_; 
v_a_8150_ = lean_ctor_get(v___x_8149_, 0);
v_a_8151_ = lean_ctor_get(v___x_8149_, 1);
v_isSharedCheck_8161_ = !lean_is_exclusive(v___x_8149_);
if (v_isSharedCheck_8161_ == 0)
{
v___x_8153_ = v___x_8149_;
v_isShared_8154_ = v_isSharedCheck_8161_;
goto v_resetjp_8152_;
}
else
{
lean_inc(v_a_8151_);
lean_inc(v_a_8150_);
lean_dec(v___x_8149_);
v___x_8153_ = lean_box(0);
v_isShared_8154_ = v_isSharedCheck_8161_;
goto v_resetjp_8152_;
}
v_resetjp_8152_:
{
lean_object* v___x_8156_; 
if (v_isShared_8139_ == 0)
{
lean_ctor_set(v___x_8138_, 0, v_a_8151_);
v___x_8156_ = v___x_8138_;
goto v_reusejp_8155_;
}
else
{
lean_object* v_reuseFailAlloc_8160_; 
v_reuseFailAlloc_8160_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8160_, 0, v_a_8151_);
lean_ctor_set(v_reuseFailAlloc_8160_, 1, v_trace_8135_);
lean_ctor_set(v_reuseFailAlloc_8160_, 2, v_buildTime_8136_);
lean_ctor_set_uint8(v_reuseFailAlloc_8160_, sizeof(void*)*3, v_action_8133_);
lean_ctor_set_uint8(v_reuseFailAlloc_8160_, sizeof(void*)*3 + 1, v_wantsRebuild_8134_);
v___x_8156_ = v_reuseFailAlloc_8160_;
goto v_reusejp_8155_;
}
v_reusejp_8155_:
{
lean_object* v___x_8158_; 
if (v_isShared_8154_ == 0)
{
lean_ctor_set(v___x_8153_, 1, v___x_8156_);
v___x_8158_ = v___x_8153_;
goto v_reusejp_8157_;
}
else
{
lean_object* v_reuseFailAlloc_8159_; 
v_reuseFailAlloc_8159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8159_, 0, v_a_8150_);
lean_ctor_set(v_reuseFailAlloc_8159_, 1, v___x_8156_);
v___x_8158_ = v_reuseFailAlloc_8159_;
goto v_reusejp_8157_;
}
v_reusejp_8157_:
{
return v___x_8158_;
}
}
}
}
else
{
lean_object* v_a_8162_; lean_object* v_a_8163_; lean_object* v___x_8165_; uint8_t v_isShared_8166_; uint8_t v_isSharedCheck_8173_; 
v_a_8162_ = lean_ctor_get(v___x_8149_, 0);
v_a_8163_ = lean_ctor_get(v___x_8149_, 1);
v_isSharedCheck_8173_ = !lean_is_exclusive(v___x_8149_);
if (v_isSharedCheck_8173_ == 0)
{
v___x_8165_ = v___x_8149_;
v_isShared_8166_ = v_isSharedCheck_8173_;
goto v_resetjp_8164_;
}
else
{
lean_inc(v_a_8163_);
lean_inc(v_a_8162_);
lean_dec(v___x_8149_);
v___x_8165_ = lean_box(0);
v_isShared_8166_ = v_isSharedCheck_8173_;
goto v_resetjp_8164_;
}
v_resetjp_8164_:
{
lean_object* v___x_8168_; 
if (v_isShared_8139_ == 0)
{
lean_ctor_set(v___x_8138_, 0, v_a_8163_);
v___x_8168_ = v___x_8138_;
goto v_reusejp_8167_;
}
else
{
lean_object* v_reuseFailAlloc_8172_; 
v_reuseFailAlloc_8172_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8172_, 0, v_a_8163_);
lean_ctor_set(v_reuseFailAlloc_8172_, 1, v_trace_8135_);
lean_ctor_set(v_reuseFailAlloc_8172_, 2, v_buildTime_8136_);
lean_ctor_set_uint8(v_reuseFailAlloc_8172_, sizeof(void*)*3, v_action_8133_);
lean_ctor_set_uint8(v_reuseFailAlloc_8172_, sizeof(void*)*3 + 1, v_wantsRebuild_8134_);
v___x_8168_ = v_reuseFailAlloc_8172_;
goto v_reusejp_8167_;
}
v_reusejp_8167_:
{
lean_object* v___x_8170_; 
if (v_isShared_8166_ == 0)
{
lean_ctor_set(v___x_8165_, 1, v___x_8168_);
v___x_8170_ = v___x_8165_;
goto v_reusejp_8169_;
}
else
{
lean_object* v_reuseFailAlloc_8171_; 
v_reuseFailAlloc_8171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8171_, 0, v_a_8162_);
lean_ctor_set(v_reuseFailAlloc_8171_, 1, v___x_8168_);
v___x_8170_ = v_reuseFailAlloc_8171_;
goto v_reusejp_8169_;
}
v_reusejp_8169_:
{
return v___x_8170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_8188_, lean_object* v_args_8189_, lean_object* v___x_8190_, lean_object* v_libFile_8191_, lean_object* v_linkDeps_8192_, lean_object* v_linkLibs_8193_, lean_object* v___y_8194_, lean_object* v___y_8195_, lean_object* v___y_8196_, lean_object* v___y_8197_, lean_object* v___y_8198_, lean_object* v___y_8199_, lean_object* v___y_8200_){
_start:
{
uint8_t v___x_34592__boxed_8201_; uint8_t v_linkDeps_boxed_8202_; lean_object* v_res_8203_; 
v___x_34592__boxed_8201_ = lean_unbox(v___x_8190_);
v_linkDeps_boxed_8202_ = lean_unbox(v_linkDeps_8192_);
v_res_8203_ = l_Lake_buildLeanSharedLibSync___lam__0(v_linkObjs_8188_, v_args_8189_, v___x_34592__boxed_8201_, v_libFile_8191_, v_linkDeps_boxed_8202_, v_linkLibs_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_, v___y_8199_);
lean_dec_ref(v___y_8198_);
lean_dec(v___y_8197_);
lean_dec(v___y_8196_);
lean_dec(v___y_8195_);
lean_dec_ref(v___y_8194_);
lean_dec_ref(v_linkLibs_8193_);
lean_dec_ref(v_args_8189_);
lean_dec_ref(v_linkObjs_8188_);
return v_res_8203_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object* v_libName_8204_, lean_object* v_libFile_8205_, lean_object* v_linkObjs_8206_, lean_object* v_linkLibs_8207_, lean_object* v_args_8208_, uint8_t v_plugin_8209_, uint8_t v_linkDeps_8210_, lean_object* v_a_8211_, lean_object* v_a_8212_, lean_object* v_a_8213_, lean_object* v_a_8214_, lean_object* v_a_8215_, lean_object* v_a_8216_){
_start:
{
lean_object* v_log_8218_; uint8_t v_action_8219_; uint8_t v_wantsRebuild_8220_; lean_object* v_trace_8221_; lean_object* v_buildTime_8222_; lean_object* v___x_8224_; uint8_t v_isShared_8225_; uint8_t v_isSharedCheck_8261_; 
v_log_8218_ = lean_ctor_get(v_a_8216_, 0);
v_action_8219_ = lean_ctor_get_uint8(v_a_8216_, sizeof(void*)*3);
v_wantsRebuild_8220_ = lean_ctor_get_uint8(v_a_8216_, sizeof(void*)*3 + 1);
v_trace_8221_ = lean_ctor_get(v_a_8216_, 1);
v_buildTime_8222_ = lean_ctor_get(v_a_8216_, 2);
v_isSharedCheck_8261_ = !lean_is_exclusive(v_a_8216_);
if (v_isSharedCheck_8261_ == 0)
{
v___x_8224_ = v_a_8216_;
v_isShared_8225_ = v_isSharedCheck_8261_;
goto v_resetjp_8223_;
}
else
{
lean_inc(v_buildTime_8222_);
lean_inc(v_trace_8221_);
lean_inc(v_log_8218_);
lean_dec(v_a_8216_);
v___x_8224_ = lean_box(0);
v_isShared_8225_ = v_isSharedCheck_8261_;
goto v_resetjp_8223_;
}
v_resetjp_8223_:
{
lean_object* v_leanTrace_8226_; lean_object* v___x_8227_; lean_object* v___x_8228_; lean_object* v___x_8229_; lean_object* v___x_8231_; 
v_leanTrace_8226_ = lean_ctor_get(v_a_8215_, 2);
lean_inc_ref(v_leanTrace_8226_);
v___x_8227_ = l_Lake_BuildTrace_mix(v_trace_8221_, v_leanTrace_8226_);
v___x_8228_ = l_Lake_platformTrace;
v___x_8229_ = l_Lake_BuildTrace_mix(v___x_8227_, v___x_8228_);
if (v_isShared_8225_ == 0)
{
lean_ctor_set(v___x_8224_, 1, v___x_8229_);
v___x_8231_ = v___x_8224_;
goto v_reusejp_8230_;
}
else
{
lean_object* v_reuseFailAlloc_8260_; 
v_reuseFailAlloc_8260_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8260_, 0, v_log_8218_);
lean_ctor_set(v_reuseFailAlloc_8260_, 1, v___x_8229_);
lean_ctor_set(v_reuseFailAlloc_8260_, 2, v_buildTime_8222_);
lean_ctor_set_uint8(v_reuseFailAlloc_8260_, sizeof(void*)*3, v_action_8219_);
lean_ctor_set_uint8(v_reuseFailAlloc_8260_, sizeof(void*)*3 + 1, v_wantsRebuild_8220_);
v___x_8231_ = v_reuseFailAlloc_8260_;
goto v_reusejp_8230_;
}
v_reusejp_8230_:
{
uint8_t v___x_8232_; lean_object* v___x_8233_; lean_object* v___x_8234_; lean_object* v___f_8235_; uint8_t v___x_8236_; lean_object* v___x_8237_; lean_object* v___x_8238_; 
v___x_8232_ = 1;
v___x_8233_ = lean_box(v___x_8232_);
v___x_8234_ = lean_box(v_linkDeps_8210_);
lean_inc_ref(v_linkLibs_8207_);
lean_inc_ref(v_libFile_8205_);
v___f_8235_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8235_, 0, v_linkObjs_8206_);
lean_closure_set(v___f_8235_, 1, v_args_8208_);
lean_closure_set(v___f_8235_, 2, v___x_8233_);
lean_closure_set(v___f_8235_, 3, v_libFile_8205_);
lean_closure_set(v___f_8235_, 4, v___x_8234_);
lean_closure_set(v___f_8235_, 5, v_linkLibs_8207_);
v___x_8236_ = 0;
v___x_8237_ = l_Lake_sharedLibExt;
v___x_8238_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8205_, v___f_8235_, v___x_8236_, v___x_8237_, v___x_8232_, v___x_8236_, v___x_8236_, v_a_8211_, v_a_8212_, v_a_8213_, v_a_8214_, v_a_8215_, v___x_8231_);
if (lean_obj_tag(v___x_8238_) == 0)
{
lean_object* v_a_8239_; lean_object* v_a_8240_; lean_object* v___x_8242_; uint8_t v_isShared_8243_; uint8_t v_isSharedCheck_8250_; 
v_a_8239_ = lean_ctor_get(v___x_8238_, 0);
v_a_8240_ = lean_ctor_get(v___x_8238_, 1);
v_isSharedCheck_8250_ = !lean_is_exclusive(v___x_8238_);
if (v_isSharedCheck_8250_ == 0)
{
v___x_8242_ = v___x_8238_;
v_isShared_8243_ = v_isSharedCheck_8250_;
goto v_resetjp_8241_;
}
else
{
lean_inc(v_a_8240_);
lean_inc(v_a_8239_);
lean_dec(v___x_8238_);
v___x_8242_ = lean_box(0);
v_isShared_8243_ = v_isSharedCheck_8250_;
goto v_resetjp_8241_;
}
v_resetjp_8241_:
{
lean_object* v_path_8244_; lean_object* v___x_8245_; lean_object* v___x_8246_; lean_object* v___x_8248_; 
v_path_8244_ = lean_ctor_get(v_a_8239_, 1);
lean_inc_ref(v_path_8244_);
lean_dec(v_a_8239_);
v___x_8245_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_8246_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8246_, 0, v_path_8244_);
lean_ctor_set(v___x_8246_, 1, v_libName_8204_);
lean_ctor_set(v___x_8246_, 2, v_linkLibs_8207_);
lean_ctor_set(v___x_8246_, 3, v___x_8245_);
lean_ctor_set_uint8(v___x_8246_, sizeof(void*)*4, v_plugin_8209_);
if (v_isShared_8243_ == 0)
{
lean_ctor_set(v___x_8242_, 0, v___x_8246_);
v___x_8248_ = v___x_8242_;
goto v_reusejp_8247_;
}
else
{
lean_object* v_reuseFailAlloc_8249_; 
v_reuseFailAlloc_8249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8249_, 0, v___x_8246_);
lean_ctor_set(v_reuseFailAlloc_8249_, 1, v_a_8240_);
v___x_8248_ = v_reuseFailAlloc_8249_;
goto v_reusejp_8247_;
}
v_reusejp_8247_:
{
return v___x_8248_;
}
}
}
else
{
lean_object* v_a_8251_; lean_object* v_a_8252_; lean_object* v___x_8254_; uint8_t v_isShared_8255_; uint8_t v_isSharedCheck_8259_; 
lean_dec_ref(v_linkLibs_8207_);
lean_dec_ref(v_libName_8204_);
v_a_8251_ = lean_ctor_get(v___x_8238_, 0);
v_a_8252_ = lean_ctor_get(v___x_8238_, 1);
v_isSharedCheck_8259_ = !lean_is_exclusive(v___x_8238_);
if (v_isSharedCheck_8259_ == 0)
{
v___x_8254_ = v___x_8238_;
v_isShared_8255_ = v_isSharedCheck_8259_;
goto v_resetjp_8253_;
}
else
{
lean_inc(v_a_8252_);
lean_inc(v_a_8251_);
lean_dec(v___x_8238_);
v___x_8254_ = lean_box(0);
v_isShared_8255_ = v_isSharedCheck_8259_;
goto v_resetjp_8253_;
}
v_resetjp_8253_:
{
lean_object* v___x_8257_; 
if (v_isShared_8255_ == 0)
{
v___x_8257_ = v___x_8254_;
goto v_reusejp_8256_;
}
else
{
lean_object* v_reuseFailAlloc_8258_; 
v_reuseFailAlloc_8258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8258_, 0, v_a_8251_);
lean_ctor_set(v_reuseFailAlloc_8258_, 1, v_a_8252_);
v___x_8257_ = v_reuseFailAlloc_8258_;
goto v_reusejp_8256_;
}
v_reusejp_8256_:
{
return v___x_8257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object* v_libName_8262_, lean_object* v_libFile_8263_, lean_object* v_linkObjs_8264_, lean_object* v_linkLibs_8265_, lean_object* v_args_8266_, lean_object* v_plugin_8267_, lean_object* v_linkDeps_8268_, lean_object* v_a_8269_, lean_object* v_a_8270_, lean_object* v_a_8271_, lean_object* v_a_8272_, lean_object* v_a_8273_, lean_object* v_a_8274_, lean_object* v_a_8275_){
_start:
{
uint8_t v_plugin_boxed_8276_; uint8_t v_linkDeps_boxed_8277_; lean_object* v_res_8278_; 
v_plugin_boxed_8276_ = lean_unbox(v_plugin_8267_);
v_linkDeps_boxed_8277_ = lean_unbox(v_linkDeps_8268_);
v_res_8278_ = l_Lake_buildLeanSharedLibSync(v_libName_8262_, v_libFile_8263_, v_linkObjs_8264_, v_linkLibs_8265_, v_args_8266_, v_plugin_boxed_8276_, v_linkDeps_boxed_8277_, v_a_8269_, v_a_8270_, v_a_8271_, v_a_8272_, v_a_8273_, v_a_8274_);
lean_dec_ref(v_a_8273_);
lean_dec(v_a_8272_);
lean_dec(v_a_8271_);
lean_dec(v_a_8270_);
return v_res_8278_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_traceArgs_8279_, lean_object* v_weakArgs_8280_, lean_object* v_libName_8281_, lean_object* v_libFile_8282_, lean_object* v_objs_8283_, uint8_t v_plugin_8284_, uint8_t v_linkDeps_8285_, lean_object* v_libs_8286_, lean_object* v___y_8287_, lean_object* v___y_8288_, lean_object* v___y_8289_, lean_object* v___y_8290_, lean_object* v___y_8291_, lean_object* v___y_8292_){
_start:
{
uint64_t v___y_8295_; uint64_t v___x_8320_; lean_object* v___x_8321_; lean_object* v___x_8322_; uint8_t v___x_8323_; 
v___x_8320_ = l_Lake_Hash_nil;
v___x_8321_ = lean_unsigned_to_nat(0u);
v___x_8322_ = lean_array_get_size(v_traceArgs_8279_);
v___x_8323_ = lean_nat_dec_lt(v___x_8321_, v___x_8322_);
if (v___x_8323_ == 0)
{
v___y_8295_ = v___x_8320_;
goto v___jp_8294_;
}
else
{
uint8_t v___x_8324_; 
v___x_8324_ = lean_nat_dec_le(v___x_8322_, v___x_8322_);
if (v___x_8324_ == 0)
{
if (v___x_8323_ == 0)
{
v___y_8295_ = v___x_8320_;
goto v___jp_8294_;
}
else
{
size_t v___x_8325_; size_t v___x_8326_; uint64_t v___x_8327_; 
v___x_8325_ = ((size_t)0ULL);
v___x_8326_ = lean_usize_of_nat(v___x_8322_);
v___x_8327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8279_, v___x_8325_, v___x_8326_, v___x_8320_);
v___y_8295_ = v___x_8327_;
goto v___jp_8294_;
}
}
else
{
size_t v___x_8328_; size_t v___x_8329_; uint64_t v___x_8330_; 
v___x_8328_ = ((size_t)0ULL);
v___x_8329_ = lean_usize_of_nat(v___x_8322_);
v___x_8330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8279_, v___x_8328_, v___x_8329_, v___x_8320_);
v___y_8295_ = v___x_8330_;
goto v___jp_8294_;
}
}
v___jp_8294_:
{
lean_object* v_log_8296_; uint8_t v_action_8297_; uint8_t v_wantsRebuild_8298_; lean_object* v_trace_8299_; lean_object* v_buildTime_8300_; lean_object* v___x_8302_; uint8_t v_isShared_8303_; uint8_t v_isSharedCheck_8319_; 
v_log_8296_ = lean_ctor_get(v___y_8292_, 0);
v_action_8297_ = lean_ctor_get_uint8(v___y_8292_, sizeof(void*)*3);
v_wantsRebuild_8298_ = lean_ctor_get_uint8(v___y_8292_, sizeof(void*)*3 + 1);
v_trace_8299_ = lean_ctor_get(v___y_8292_, 1);
v_buildTime_8300_ = lean_ctor_get(v___y_8292_, 2);
v_isSharedCheck_8319_ = !lean_is_exclusive(v___y_8292_);
if (v_isSharedCheck_8319_ == 0)
{
v___x_8302_ = v___y_8292_;
v_isShared_8303_ = v_isSharedCheck_8319_;
goto v_resetjp_8301_;
}
else
{
lean_inc(v_buildTime_8300_);
lean_inc(v_trace_8299_);
lean_inc(v_log_8296_);
lean_dec(v___y_8292_);
v___x_8302_ = lean_box(0);
v_isShared_8303_ = v_isSharedCheck_8319_;
goto v_resetjp_8301_;
}
v_resetjp_8301_:
{
lean_object* v___x_8304_; lean_object* v___x_8305_; lean_object* v___x_8306_; lean_object* v___x_8307_; lean_object* v___x_8308_; lean_object* v___x_8309_; lean_object* v___x_8310_; lean_object* v___x_8311_; lean_object* v___x_8312_; lean_object* v___x_8313_; lean_object* v___x_8315_; 
v___x_8304_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8305_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8306_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8279_);
v___x_8307_ = lean_array_to_list(v_traceArgs_8279_);
v___x_8308_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8307_);
lean_dec(v___x_8307_);
v___x_8309_ = lean_string_append(v___x_8306_, v___x_8308_);
lean_dec_ref(v___x_8308_);
v___x_8310_ = lean_string_append(v___x_8305_, v___x_8309_);
lean_dec_ref(v___x_8309_);
v___x_8311_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8312_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8312_, 0, v___x_8310_);
lean_ctor_set(v___x_8312_, 1, v___x_8304_);
lean_ctor_set(v___x_8312_, 2, v___x_8311_);
lean_ctor_set_uint64(v___x_8312_, sizeof(void*)*3, v___y_8295_);
v___x_8313_ = l_Lake_BuildTrace_mix(v_trace_8299_, v___x_8312_);
if (v_isShared_8303_ == 0)
{
lean_ctor_set(v___x_8302_, 1, v___x_8313_);
v___x_8315_ = v___x_8302_;
goto v_reusejp_8314_;
}
else
{
lean_object* v_reuseFailAlloc_8318_; 
v_reuseFailAlloc_8318_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8318_, 0, v_log_8296_);
lean_ctor_set(v_reuseFailAlloc_8318_, 1, v___x_8313_);
lean_ctor_set(v_reuseFailAlloc_8318_, 2, v_buildTime_8300_);
lean_ctor_set_uint8(v_reuseFailAlloc_8318_, sizeof(void*)*3, v_action_8297_);
lean_ctor_set_uint8(v_reuseFailAlloc_8318_, sizeof(void*)*3 + 1, v_wantsRebuild_8298_);
v___x_8315_ = v_reuseFailAlloc_8318_;
goto v_reusejp_8314_;
}
v_reusejp_8314_:
{
lean_object* v___x_8316_; lean_object* v___x_8317_; 
v___x_8316_ = l_Array_append___redArg(v_weakArgs_8280_, v_traceArgs_8279_);
lean_dec_ref(v_traceArgs_8279_);
v___x_8317_ = l_Lake_buildLeanSharedLibSync(v_libName_8281_, v_libFile_8282_, v_objs_8283_, v_libs_8286_, v___x_8316_, v_plugin_8284_, v_linkDeps_8285_, v___y_8287_, v___y_8288_, v___y_8289_, v___y_8290_, v___y_8291_, v___x_8315_);
return v___x_8317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_traceArgs_8331_, lean_object* v_weakArgs_8332_, lean_object* v_libName_8333_, lean_object* v_libFile_8334_, lean_object* v_objs_8335_, lean_object* v_plugin_8336_, lean_object* v_linkDeps_8337_, lean_object* v_libs_8338_, lean_object* v___y_8339_, lean_object* v___y_8340_, lean_object* v___y_8341_, lean_object* v___y_8342_, lean_object* v___y_8343_, lean_object* v___y_8344_, lean_object* v___y_8345_){
_start:
{
uint8_t v_plugin_boxed_8346_; uint8_t v_linkDeps_boxed_8347_; lean_object* v_res_8348_; 
v_plugin_boxed_8346_ = lean_unbox(v_plugin_8336_);
v_linkDeps_boxed_8347_ = lean_unbox(v_linkDeps_8337_);
v_res_8348_ = l_Lake_buildLeanSharedLib___lam__0(v_traceArgs_8331_, v_weakArgs_8332_, v_libName_8333_, v_libFile_8334_, v_objs_8335_, v_plugin_boxed_8346_, v_linkDeps_boxed_8347_, v_libs_8338_, v___y_8339_, v___y_8340_, v___y_8341_, v___y_8342_, v___y_8343_, v___y_8344_);
lean_dec_ref(v___y_8343_);
lean_dec(v___y_8342_);
lean_dec(v___y_8341_);
lean_dec(v___y_8340_);
return v_res_8348_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_traceArgs_8349_, lean_object* v_weakArgs_8350_, lean_object* v_libName_8351_, lean_object* v_libFile_8352_, uint8_t v_plugin_8353_, uint8_t v_linkDeps_8354_, lean_object* v_linkLibs_8355_, lean_object* v___x_8356_, lean_object* v_objs_8357_, lean_object* v___y_8358_, lean_object* v___y_8359_, lean_object* v___y_8360_, lean_object* v___y_8361_, lean_object* v___y_8362_, lean_object* v___y_8363_){
_start:
{
lean_object* v_trace_8365_; lean_object* v___x_8366_; lean_object* v___x_8367_; lean_object* v___f_8368_; lean_object* v___x_8369_; lean_object* v___x_8370_; lean_object* v___x_8371_; uint8_t v___x_8372_; lean_object* v___x_8373_; lean_object* v___x_8374_; 
v_trace_8365_ = lean_ctor_get(v___y_8363_, 1);
v___x_8366_ = lean_box(v_plugin_8353_);
v___x_8367_ = lean_box(v_linkDeps_8354_);
v___f_8368_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 15, 7);
lean_closure_set(v___f_8368_, 0, v_traceArgs_8349_);
lean_closure_set(v___f_8368_, 1, v_weakArgs_8350_);
lean_closure_set(v___f_8368_, 2, v_libName_8351_);
lean_closure_set(v___f_8368_, 3, v_libFile_8352_);
lean_closure_set(v___f_8368_, 4, v_objs_8357_);
lean_closure_set(v___f_8368_, 5, v___x_8366_);
lean_closure_set(v___f_8368_, 6, v___x_8367_);
v___x_8369_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8370_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8355_, v___x_8369_);
v___x_8371_ = lean_unsigned_to_nat(0u);
v___x_8372_ = 0;
v___x_8373_ = l_Lake_Job_mapM___redArg(v___x_8356_, v___x_8370_, v___f_8368_, v___x_8371_, v___x_8372_, v___y_8358_, v___y_8359_, v___y_8360_, v___y_8361_, v___y_8362_, v_trace_8365_);
v___x_8374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8374_, 0, v___x_8373_);
lean_ctor_set(v___x_8374_, 1, v___y_8363_);
return v___x_8374_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_traceArgs_8375_, lean_object* v_weakArgs_8376_, lean_object* v_libName_8377_, lean_object* v_libFile_8378_, lean_object* v_plugin_8379_, lean_object* v_linkDeps_8380_, lean_object* v_linkLibs_8381_, lean_object* v___x_8382_, lean_object* v_objs_8383_, lean_object* v___y_8384_, lean_object* v___y_8385_, lean_object* v___y_8386_, lean_object* v___y_8387_, lean_object* v___y_8388_, lean_object* v___y_8389_, lean_object* v___y_8390_){
_start:
{
uint8_t v_plugin_boxed_8391_; uint8_t v_linkDeps_boxed_8392_; lean_object* v_res_8393_; 
v_plugin_boxed_8391_ = lean_unbox(v_plugin_8379_);
v_linkDeps_boxed_8392_ = lean_unbox(v_linkDeps_8380_);
v_res_8393_ = l_Lake_buildLeanSharedLib___lam__1(v_traceArgs_8375_, v_weakArgs_8376_, v_libName_8377_, v_libFile_8378_, v_plugin_boxed_8391_, v_linkDeps_boxed_8392_, v_linkLibs_8381_, v___x_8382_, v_objs_8383_, v___y_8384_, v___y_8385_, v___y_8386_, v___y_8387_, v___y_8388_, v___y_8389_);
lean_dec_ref(v___y_8388_);
lean_dec(v___y_8387_);
lean_dec(v___y_8386_);
lean_dec(v___y_8385_);
lean_dec_ref(v_linkLibs_8381_);
return v_res_8393_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8394_, lean_object* v_libFile_8395_, lean_object* v_linkObjs_8396_, lean_object* v_linkLibs_8397_, lean_object* v_weakArgs_8398_, lean_object* v_traceArgs_8399_, uint8_t v_plugin_8400_, uint8_t v_linkDeps_8401_, lean_object* v_a_8402_, lean_object* v_a_8403_, lean_object* v_a_8404_, lean_object* v_a_8405_, lean_object* v_a_8406_, lean_object* v_a_8407_){
_start:
{
lean_object* v___x_8409_; lean_object* v___x_8410_; lean_object* v___x_8411_; lean_object* v___f_8412_; lean_object* v___x_8413_; lean_object* v___x_8414_; lean_object* v___x_8415_; uint8_t v___x_8416_; lean_object* v___x_8417_; 
v___x_8409_ = l_Lake_instDataKindDynlib;
v___x_8410_ = lean_box(v_plugin_8400_);
v___x_8411_ = lean_box(v_linkDeps_8401_);
v___f_8412_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 16, 8);
lean_closure_set(v___f_8412_, 0, v_traceArgs_8399_);
lean_closure_set(v___f_8412_, 1, v_weakArgs_8398_);
lean_closure_set(v___f_8412_, 2, v_libName_8394_);
lean_closure_set(v___f_8412_, 3, v_libFile_8395_);
lean_closure_set(v___f_8412_, 4, v___x_8410_);
lean_closure_set(v___f_8412_, 5, v___x_8411_);
lean_closure_set(v___f_8412_, 6, v_linkLibs_8397_);
lean_closure_set(v___f_8412_, 7, v___x_8409_);
v___x_8413_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8414_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8396_, v___x_8413_);
v___x_8415_ = lean_unsigned_to_nat(0u);
v___x_8416_ = 1;
v___x_8417_ = l_Lake_Job_bindM___redArg(v___x_8409_, v___x_8414_, v___f_8412_, v___x_8415_, v___x_8416_, v_a_8402_, v_a_8403_, v_a_8404_, v_a_8405_, v_a_8406_, v_a_8407_);
return v___x_8417_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8418_, lean_object* v_libFile_8419_, lean_object* v_linkObjs_8420_, lean_object* v_linkLibs_8421_, lean_object* v_weakArgs_8422_, lean_object* v_traceArgs_8423_, lean_object* v_plugin_8424_, lean_object* v_linkDeps_8425_, lean_object* v_a_8426_, lean_object* v_a_8427_, lean_object* v_a_8428_, lean_object* v_a_8429_, lean_object* v_a_8430_, lean_object* v_a_8431_, lean_object* v_a_8432_){
_start:
{
uint8_t v_plugin_boxed_8433_; uint8_t v_linkDeps_boxed_8434_; lean_object* v_res_8435_; 
v_plugin_boxed_8433_ = lean_unbox(v_plugin_8424_);
v_linkDeps_boxed_8434_ = lean_unbox(v_linkDeps_8425_);
v_res_8435_ = l_Lake_buildLeanSharedLib(v_libName_8418_, v_libFile_8419_, v_linkObjs_8420_, v_linkLibs_8421_, v_weakArgs_8422_, v_traceArgs_8423_, v_plugin_boxed_8433_, v_linkDeps_boxed_8434_, v_a_8426_, v_a_8427_, v_a_8428_, v_a_8429_, v_a_8430_, v_a_8431_);
lean_dec_ref(v_a_8431_);
lean_dec_ref(v_a_8430_);
lean_dec(v_a_8429_);
lean_dec(v_a_8428_);
lean_dec(v_a_8427_);
lean_dec_ref(v_linkObjs_8420_);
return v_res_8435_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object* v_linkLibs_8436_, lean_object* v_linkObjs_8437_, lean_object* v_args_8438_, uint8_t v_sharedLean_8439_, lean_object* v_exeFile_8440_, lean_object* v___y_8441_, lean_object* v___y_8442_, lean_object* v___y_8443_, lean_object* v___y_8444_, lean_object* v___y_8445_, lean_object* v___y_8446_){
_start:
{
lean_object* v___x_8448_; 
v___x_8448_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8436_, v___y_8446_);
if (lean_obj_tag(v___x_8448_) == 0)
{
lean_object* v_toContext_8449_; lean_object* v_lakeEnv_8450_; lean_object* v_lean_8451_; lean_object* v_a_8452_; lean_object* v_a_8453_; lean_object* v_leanLibDir_8454_; lean_object* v_cc_8455_; lean_object* v_log_8456_; uint8_t v_action_8457_; uint8_t v_wantsRebuild_8458_; lean_object* v_trace_8459_; lean_object* v_buildTime_8460_; lean_object* v___x_8462_; uint8_t v_isShared_8463_; uint8_t v_isSharedCheck_8498_; 
v_toContext_8449_ = lean_ctor_get(v___y_8445_, 1);
v_lakeEnv_8450_ = lean_ctor_get(v_toContext_8449_, 0);
v_lean_8451_ = lean_ctor_get(v_lakeEnv_8450_, 1);
v_a_8452_ = lean_ctor_get(v___x_8448_, 1);
lean_inc(v_a_8452_);
v_a_8453_ = lean_ctor_get(v___x_8448_, 0);
lean_inc(v_a_8453_);
lean_dec_ref_known(v___x_8448_, 2);
v_leanLibDir_8454_ = lean_ctor_get(v_lean_8451_, 3);
v_cc_8455_ = lean_ctor_get(v_lean_8451_, 14);
v_log_8456_ = lean_ctor_get(v_a_8452_, 0);
v_action_8457_ = lean_ctor_get_uint8(v_a_8452_, sizeof(void*)*3);
v_wantsRebuild_8458_ = lean_ctor_get_uint8(v_a_8452_, sizeof(void*)*3 + 1);
v_trace_8459_ = lean_ctor_get(v_a_8452_, 1);
v_buildTime_8460_ = lean_ctor_get(v_a_8452_, 2);
v_isSharedCheck_8498_ = !lean_is_exclusive(v_a_8452_);
if (v_isSharedCheck_8498_ == 0)
{
v___x_8462_ = v_a_8452_;
v_isShared_8463_ = v_isSharedCheck_8498_;
goto v_resetjp_8461_;
}
else
{
lean_inc(v_buildTime_8460_);
lean_inc(v_trace_8459_);
lean_inc(v_log_8456_);
lean_dec(v_a_8452_);
v___x_8462_ = lean_box(0);
v_isShared_8463_ = v_isSharedCheck_8498_;
goto v_resetjp_8461_;
}
v_resetjp_8461_:
{
lean_object* v___x_8464_; lean_object* v___x_8465_; lean_object* v___x_8466_; lean_object* v___x_8467_; lean_object* v___x_8468_; lean_object* v___x_8469_; lean_object* v___x_8470_; lean_object* v___x_8471_; lean_object* v___x_8472_; lean_object* v___x_8473_; 
v___x_8464_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8437_, v_a_8453_);
lean_dec(v_a_8453_);
v___x_8465_ = l_Array_append___redArg(v___x_8464_, v_args_8438_);
v___x_8466_ = lean_unsigned_to_nat(2u);
v___x_8467_ = lean_mk_empty_array_with_capacity(v___x_8466_);
lean_dec_ref(v___x_8467_);
v___x_8468_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8454_);
v___x_8469_ = lean_array_push(v___x_8468_, v_leanLibDir_8454_);
v___x_8470_ = l_Array_append___redArg(v___x_8465_, v___x_8469_);
lean_dec_ref(v___x_8469_);
v___x_8471_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8439_, v_lean_8451_);
v___x_8472_ = l_Array_append___redArg(v___x_8470_, v___x_8471_);
lean_dec_ref(v___x_8471_);
lean_inc_ref(v_cc_8455_);
v___x_8473_ = l_Lake_compileExe(v_exeFile_8440_, v___x_8472_, v_cc_8455_, v_log_8456_);
lean_dec_ref(v___x_8472_);
if (lean_obj_tag(v___x_8473_) == 0)
{
lean_object* v_a_8474_; lean_object* v_a_8475_; lean_object* v___x_8477_; uint8_t v_isShared_8478_; uint8_t v_isSharedCheck_8485_; 
v_a_8474_ = lean_ctor_get(v___x_8473_, 0);
v_a_8475_ = lean_ctor_get(v___x_8473_, 1);
v_isSharedCheck_8485_ = !lean_is_exclusive(v___x_8473_);
if (v_isSharedCheck_8485_ == 0)
{
v___x_8477_ = v___x_8473_;
v_isShared_8478_ = v_isSharedCheck_8485_;
goto v_resetjp_8476_;
}
else
{
lean_inc(v_a_8475_);
lean_inc(v_a_8474_);
lean_dec(v___x_8473_);
v___x_8477_ = lean_box(0);
v_isShared_8478_ = v_isSharedCheck_8485_;
goto v_resetjp_8476_;
}
v_resetjp_8476_:
{
lean_object* v___x_8480_; 
if (v_isShared_8463_ == 0)
{
lean_ctor_set(v___x_8462_, 0, v_a_8475_);
v___x_8480_ = v___x_8462_;
goto v_reusejp_8479_;
}
else
{
lean_object* v_reuseFailAlloc_8484_; 
v_reuseFailAlloc_8484_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8484_, 0, v_a_8475_);
lean_ctor_set(v_reuseFailAlloc_8484_, 1, v_trace_8459_);
lean_ctor_set(v_reuseFailAlloc_8484_, 2, v_buildTime_8460_);
lean_ctor_set_uint8(v_reuseFailAlloc_8484_, sizeof(void*)*3, v_action_8457_);
lean_ctor_set_uint8(v_reuseFailAlloc_8484_, sizeof(void*)*3 + 1, v_wantsRebuild_8458_);
v___x_8480_ = v_reuseFailAlloc_8484_;
goto v_reusejp_8479_;
}
v_reusejp_8479_:
{
lean_object* v___x_8482_; 
if (v_isShared_8478_ == 0)
{
lean_ctor_set(v___x_8477_, 1, v___x_8480_);
v___x_8482_ = v___x_8477_;
goto v_reusejp_8481_;
}
else
{
lean_object* v_reuseFailAlloc_8483_; 
v_reuseFailAlloc_8483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8483_, 0, v_a_8474_);
lean_ctor_set(v_reuseFailAlloc_8483_, 1, v___x_8480_);
v___x_8482_ = v_reuseFailAlloc_8483_;
goto v_reusejp_8481_;
}
v_reusejp_8481_:
{
return v___x_8482_;
}
}
}
}
else
{
lean_object* v_a_8486_; lean_object* v_a_8487_; lean_object* v___x_8489_; uint8_t v_isShared_8490_; uint8_t v_isSharedCheck_8497_; 
v_a_8486_ = lean_ctor_get(v___x_8473_, 0);
v_a_8487_ = lean_ctor_get(v___x_8473_, 1);
v_isSharedCheck_8497_ = !lean_is_exclusive(v___x_8473_);
if (v_isSharedCheck_8497_ == 0)
{
v___x_8489_ = v___x_8473_;
v_isShared_8490_ = v_isSharedCheck_8497_;
goto v_resetjp_8488_;
}
else
{
lean_inc(v_a_8487_);
lean_inc(v_a_8486_);
lean_dec(v___x_8473_);
v___x_8489_ = lean_box(0);
v_isShared_8490_ = v_isSharedCheck_8497_;
goto v_resetjp_8488_;
}
v_resetjp_8488_:
{
lean_object* v___x_8492_; 
if (v_isShared_8463_ == 0)
{
lean_ctor_set(v___x_8462_, 0, v_a_8487_);
v___x_8492_ = v___x_8462_;
goto v_reusejp_8491_;
}
else
{
lean_object* v_reuseFailAlloc_8496_; 
v_reuseFailAlloc_8496_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8496_, 0, v_a_8487_);
lean_ctor_set(v_reuseFailAlloc_8496_, 1, v_trace_8459_);
lean_ctor_set(v_reuseFailAlloc_8496_, 2, v_buildTime_8460_);
lean_ctor_set_uint8(v_reuseFailAlloc_8496_, sizeof(void*)*3, v_action_8457_);
lean_ctor_set_uint8(v_reuseFailAlloc_8496_, sizeof(void*)*3 + 1, v_wantsRebuild_8458_);
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
v_reuseFailAlloc_8495_ = lean_alloc_ctor(1, 2, 0);
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
}
}
else
{
lean_object* v_a_8499_; lean_object* v_a_8500_; lean_object* v___x_8502_; uint8_t v_isShared_8503_; uint8_t v_isSharedCheck_8507_; 
lean_dec_ref(v_exeFile_8440_);
v_a_8499_ = lean_ctor_get(v___x_8448_, 0);
v_a_8500_ = lean_ctor_get(v___x_8448_, 1);
v_isSharedCheck_8507_ = !lean_is_exclusive(v___x_8448_);
if (v_isSharedCheck_8507_ == 0)
{
v___x_8502_ = v___x_8448_;
v_isShared_8503_ = v_isSharedCheck_8507_;
goto v_resetjp_8501_;
}
else
{
lean_inc(v_a_8500_);
lean_inc(v_a_8499_);
lean_dec(v___x_8448_);
v___x_8502_ = lean_box(0);
v_isShared_8503_ = v_isSharedCheck_8507_;
goto v_resetjp_8501_;
}
v_resetjp_8501_:
{
lean_object* v___x_8505_; 
if (v_isShared_8503_ == 0)
{
v___x_8505_ = v___x_8502_;
goto v_reusejp_8504_;
}
else
{
lean_object* v_reuseFailAlloc_8506_; 
v_reuseFailAlloc_8506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8506_, 0, v_a_8499_);
lean_ctor_set(v_reuseFailAlloc_8506_, 1, v_a_8500_);
v___x_8505_ = v_reuseFailAlloc_8506_;
goto v_reusejp_8504_;
}
v_reusejp_8504_:
{
return v___x_8505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object* v_linkLibs_8508_, lean_object* v_linkObjs_8509_, lean_object* v_args_8510_, lean_object* v_sharedLean_8511_, lean_object* v_exeFile_8512_, lean_object* v___y_8513_, lean_object* v___y_8514_, lean_object* v___y_8515_, lean_object* v___y_8516_, lean_object* v___y_8517_, lean_object* v___y_8518_, lean_object* v___y_8519_){
_start:
{
uint8_t v_sharedLean_boxed_8520_; lean_object* v_res_8521_; 
v_sharedLean_boxed_8520_ = lean_unbox(v_sharedLean_8511_);
v_res_8521_ = l_Lake_buildLeanExeSync___lam__0(v_linkLibs_8508_, v_linkObjs_8509_, v_args_8510_, v_sharedLean_boxed_8520_, v_exeFile_8512_, v___y_8513_, v___y_8514_, v___y_8515_, v___y_8516_, v___y_8517_, v___y_8518_);
lean_dec_ref(v___y_8517_);
lean_dec(v___y_8516_);
lean_dec(v___y_8515_);
lean_dec(v___y_8514_);
lean_dec_ref(v___y_8513_);
lean_dec_ref(v_args_8510_);
lean_dec_ref(v_linkObjs_8509_);
lean_dec_ref(v_linkLibs_8508_);
return v_res_8521_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object* v_exeFile_8522_, lean_object* v_linkObjs_8523_, lean_object* v_linkLibs_8524_, lean_object* v_args_8525_, uint8_t v_sharedLean_8526_, lean_object* v_a_8527_, lean_object* v_a_8528_, lean_object* v_a_8529_, lean_object* v_a_8530_, lean_object* v_a_8531_, lean_object* v_a_8532_){
_start:
{
lean_object* v_log_8534_; uint8_t v_action_8535_; uint8_t v_wantsRebuild_8536_; lean_object* v_trace_8537_; lean_object* v_buildTime_8538_; lean_object* v___x_8540_; uint8_t v_isShared_8541_; uint8_t v_isSharedCheck_8574_; 
v_log_8534_ = lean_ctor_get(v_a_8532_, 0);
v_action_8535_ = lean_ctor_get_uint8(v_a_8532_, sizeof(void*)*3);
v_wantsRebuild_8536_ = lean_ctor_get_uint8(v_a_8532_, sizeof(void*)*3 + 1);
v_trace_8537_ = lean_ctor_get(v_a_8532_, 1);
v_buildTime_8538_ = lean_ctor_get(v_a_8532_, 2);
v_isSharedCheck_8574_ = !lean_is_exclusive(v_a_8532_);
if (v_isSharedCheck_8574_ == 0)
{
v___x_8540_ = v_a_8532_;
v_isShared_8541_ = v_isSharedCheck_8574_;
goto v_resetjp_8539_;
}
else
{
lean_inc(v_buildTime_8538_);
lean_inc(v_trace_8537_);
lean_inc(v_log_8534_);
lean_dec(v_a_8532_);
v___x_8540_ = lean_box(0);
v_isShared_8541_ = v_isSharedCheck_8574_;
goto v_resetjp_8539_;
}
v_resetjp_8539_:
{
lean_object* v_leanTrace_8542_; lean_object* v___x_8543_; lean_object* v___f_8544_; lean_object* v___x_8545_; lean_object* v___x_8546_; lean_object* v___x_8547_; lean_object* v___x_8549_; 
v_leanTrace_8542_ = lean_ctor_get(v_a_8531_, 2);
v___x_8543_ = lean_box(v_sharedLean_8526_);
lean_inc_ref(v_exeFile_8522_);
v___f_8544_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 12, 5);
lean_closure_set(v___f_8544_, 0, v_linkLibs_8524_);
lean_closure_set(v___f_8544_, 1, v_linkObjs_8523_);
lean_closure_set(v___f_8544_, 2, v_args_8525_);
lean_closure_set(v___f_8544_, 3, v___x_8543_);
lean_closure_set(v___f_8544_, 4, v_exeFile_8522_);
lean_inc_ref(v_leanTrace_8542_);
v___x_8545_ = l_Lake_BuildTrace_mix(v_trace_8537_, v_leanTrace_8542_);
v___x_8546_ = l_Lake_platformTrace;
v___x_8547_ = l_Lake_BuildTrace_mix(v___x_8545_, v___x_8546_);
if (v_isShared_8541_ == 0)
{
lean_ctor_set(v___x_8540_, 1, v___x_8547_);
v___x_8549_ = v___x_8540_;
goto v_reusejp_8548_;
}
else
{
lean_object* v_reuseFailAlloc_8573_; 
v_reuseFailAlloc_8573_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8573_, 0, v_log_8534_);
lean_ctor_set(v_reuseFailAlloc_8573_, 1, v___x_8547_);
lean_ctor_set(v_reuseFailAlloc_8573_, 2, v_buildTime_8538_);
lean_ctor_set_uint8(v_reuseFailAlloc_8573_, sizeof(void*)*3, v_action_8535_);
lean_ctor_set_uint8(v_reuseFailAlloc_8573_, sizeof(void*)*3 + 1, v_wantsRebuild_8536_);
v___x_8549_ = v_reuseFailAlloc_8573_;
goto v_reusejp_8548_;
}
v_reusejp_8548_:
{
uint8_t v___x_8550_; uint8_t v___x_8551_; lean_object* v___x_8552_; lean_object* v___x_8553_; 
v___x_8550_ = 1;
v___x_8551_ = 0;
v___x_8552_ = l_System_FilePath_exeExtension;
v___x_8553_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8522_, v___f_8544_, v___x_8551_, v___x_8552_, v___x_8550_, v___x_8550_, v___x_8551_, v_a_8527_, v_a_8528_, v_a_8529_, v_a_8530_, v_a_8531_, v___x_8549_);
if (lean_obj_tag(v___x_8553_) == 0)
{
lean_object* v_a_8554_; lean_object* v_a_8555_; lean_object* v___x_8557_; uint8_t v_isShared_8558_; uint8_t v_isSharedCheck_8563_; 
v_a_8554_ = lean_ctor_get(v___x_8553_, 0);
v_a_8555_ = lean_ctor_get(v___x_8553_, 1);
v_isSharedCheck_8563_ = !lean_is_exclusive(v___x_8553_);
if (v_isSharedCheck_8563_ == 0)
{
v___x_8557_ = v___x_8553_;
v_isShared_8558_ = v_isSharedCheck_8563_;
goto v_resetjp_8556_;
}
else
{
lean_inc(v_a_8555_);
lean_inc(v_a_8554_);
lean_dec(v___x_8553_);
v___x_8557_ = lean_box(0);
v_isShared_8558_ = v_isSharedCheck_8563_;
goto v_resetjp_8556_;
}
v_resetjp_8556_:
{
lean_object* v_path_8559_; lean_object* v___x_8561_; 
v_path_8559_ = lean_ctor_get(v_a_8554_, 1);
lean_inc_ref(v_path_8559_);
lean_dec(v_a_8554_);
if (v_isShared_8558_ == 0)
{
lean_ctor_set(v___x_8557_, 0, v_path_8559_);
v___x_8561_ = v___x_8557_;
goto v_reusejp_8560_;
}
else
{
lean_object* v_reuseFailAlloc_8562_; 
v_reuseFailAlloc_8562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8562_, 0, v_path_8559_);
lean_ctor_set(v_reuseFailAlloc_8562_, 1, v_a_8555_);
v___x_8561_ = v_reuseFailAlloc_8562_;
goto v_reusejp_8560_;
}
v_reusejp_8560_:
{
return v___x_8561_;
}
}
}
else
{
lean_object* v_a_8564_; lean_object* v_a_8565_; lean_object* v___x_8567_; uint8_t v_isShared_8568_; uint8_t v_isSharedCheck_8572_; 
v_a_8564_ = lean_ctor_get(v___x_8553_, 0);
v_a_8565_ = lean_ctor_get(v___x_8553_, 1);
v_isSharedCheck_8572_ = !lean_is_exclusive(v___x_8553_);
if (v_isSharedCheck_8572_ == 0)
{
v___x_8567_ = v___x_8553_;
v_isShared_8568_ = v_isSharedCheck_8572_;
goto v_resetjp_8566_;
}
else
{
lean_inc(v_a_8565_);
lean_inc(v_a_8564_);
lean_dec(v___x_8553_);
v___x_8567_ = lean_box(0);
v_isShared_8568_ = v_isSharedCheck_8572_;
goto v_resetjp_8566_;
}
v_resetjp_8566_:
{
lean_object* v___x_8570_; 
if (v_isShared_8568_ == 0)
{
v___x_8570_ = v___x_8567_;
goto v_reusejp_8569_;
}
else
{
lean_object* v_reuseFailAlloc_8571_; 
v_reuseFailAlloc_8571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8571_, 0, v_a_8564_);
lean_ctor_set(v_reuseFailAlloc_8571_, 1, v_a_8565_);
v___x_8570_ = v_reuseFailAlloc_8571_;
goto v_reusejp_8569_;
}
v_reusejp_8569_:
{
return v___x_8570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object* v_exeFile_8575_, lean_object* v_linkObjs_8576_, lean_object* v_linkLibs_8577_, lean_object* v_args_8578_, lean_object* v_sharedLean_8579_, lean_object* v_a_8580_, lean_object* v_a_8581_, lean_object* v_a_8582_, lean_object* v_a_8583_, lean_object* v_a_8584_, lean_object* v_a_8585_, lean_object* v_a_8586_){
_start:
{
uint8_t v_sharedLean_boxed_8587_; lean_object* v_res_8588_; 
v_sharedLean_boxed_8587_ = lean_unbox(v_sharedLean_8579_);
v_res_8588_ = l_Lake_buildLeanExeSync(v_exeFile_8575_, v_linkObjs_8576_, v_linkLibs_8577_, v_args_8578_, v_sharedLean_boxed_8587_, v_a_8580_, v_a_8581_, v_a_8582_, v_a_8583_, v_a_8584_, v_a_8585_);
lean_dec_ref(v_a_8584_);
lean_dec(v_a_8583_);
lean_dec(v_a_8582_);
lean_dec(v_a_8581_);
return v_res_8588_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_traceArgs_8589_, lean_object* v_weakArgs_8590_, lean_object* v_exeFile_8591_, lean_object* v_objs_8592_, uint8_t v_sharedLean_8593_, lean_object* v_libs_8594_, lean_object* v___y_8595_, lean_object* v___y_8596_, lean_object* v___y_8597_, lean_object* v___y_8598_, lean_object* v___y_8599_, lean_object* v___y_8600_){
_start:
{
uint64_t v___y_8603_; uint64_t v___x_8628_; lean_object* v___x_8629_; lean_object* v___x_8630_; uint8_t v___x_8631_; 
v___x_8628_ = l_Lake_Hash_nil;
v___x_8629_ = lean_unsigned_to_nat(0u);
v___x_8630_ = lean_array_get_size(v_traceArgs_8589_);
v___x_8631_ = lean_nat_dec_lt(v___x_8629_, v___x_8630_);
if (v___x_8631_ == 0)
{
v___y_8603_ = v___x_8628_;
goto v___jp_8602_;
}
else
{
uint8_t v___x_8632_; 
v___x_8632_ = lean_nat_dec_le(v___x_8630_, v___x_8630_);
if (v___x_8632_ == 0)
{
if (v___x_8631_ == 0)
{
v___y_8603_ = v___x_8628_;
goto v___jp_8602_;
}
else
{
size_t v___x_8633_; size_t v___x_8634_; uint64_t v___x_8635_; 
v___x_8633_ = ((size_t)0ULL);
v___x_8634_ = lean_usize_of_nat(v___x_8630_);
v___x_8635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8589_, v___x_8633_, v___x_8634_, v___x_8628_);
v___y_8603_ = v___x_8635_;
goto v___jp_8602_;
}
}
else
{
size_t v___x_8636_; size_t v___x_8637_; uint64_t v___x_8638_; 
v___x_8636_ = ((size_t)0ULL);
v___x_8637_ = lean_usize_of_nat(v___x_8630_);
v___x_8638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8589_, v___x_8636_, v___x_8637_, v___x_8628_);
v___y_8603_ = v___x_8638_;
goto v___jp_8602_;
}
}
v___jp_8602_:
{
lean_object* v_log_8604_; uint8_t v_action_8605_; uint8_t v_wantsRebuild_8606_; lean_object* v_trace_8607_; lean_object* v_buildTime_8608_; lean_object* v___x_8610_; uint8_t v_isShared_8611_; uint8_t v_isSharedCheck_8627_; 
v_log_8604_ = lean_ctor_get(v___y_8600_, 0);
v_action_8605_ = lean_ctor_get_uint8(v___y_8600_, sizeof(void*)*3);
v_wantsRebuild_8606_ = lean_ctor_get_uint8(v___y_8600_, sizeof(void*)*3 + 1);
v_trace_8607_ = lean_ctor_get(v___y_8600_, 1);
v_buildTime_8608_ = lean_ctor_get(v___y_8600_, 2);
v_isSharedCheck_8627_ = !lean_is_exclusive(v___y_8600_);
if (v_isSharedCheck_8627_ == 0)
{
v___x_8610_ = v___y_8600_;
v_isShared_8611_ = v_isSharedCheck_8627_;
goto v_resetjp_8609_;
}
else
{
lean_inc(v_buildTime_8608_);
lean_inc(v_trace_8607_);
lean_inc(v_log_8604_);
lean_dec(v___y_8600_);
v___x_8610_ = lean_box(0);
v_isShared_8611_ = v_isSharedCheck_8627_;
goto v_resetjp_8609_;
}
v_resetjp_8609_:
{
lean_object* v___x_8612_; lean_object* v___x_8613_; lean_object* v___x_8614_; lean_object* v___x_8615_; lean_object* v___x_8616_; lean_object* v___x_8617_; lean_object* v___x_8618_; lean_object* v___x_8619_; lean_object* v___x_8620_; lean_object* v___x_8621_; lean_object* v___x_8623_; 
v___x_8612_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8613_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8614_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8589_);
v___x_8615_ = lean_array_to_list(v_traceArgs_8589_);
v___x_8616_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8615_);
lean_dec(v___x_8615_);
v___x_8617_ = lean_string_append(v___x_8614_, v___x_8616_);
lean_dec_ref(v___x_8616_);
v___x_8618_ = lean_string_append(v___x_8613_, v___x_8617_);
lean_dec_ref(v___x_8617_);
v___x_8619_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8620_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8620_, 0, v___x_8618_);
lean_ctor_set(v___x_8620_, 1, v___x_8612_);
lean_ctor_set(v___x_8620_, 2, v___x_8619_);
lean_ctor_set_uint64(v___x_8620_, sizeof(void*)*3, v___y_8603_);
v___x_8621_ = l_Lake_BuildTrace_mix(v_trace_8607_, v___x_8620_);
if (v_isShared_8611_ == 0)
{
lean_ctor_set(v___x_8610_, 1, v___x_8621_);
v___x_8623_ = v___x_8610_;
goto v_reusejp_8622_;
}
else
{
lean_object* v_reuseFailAlloc_8626_; 
v_reuseFailAlloc_8626_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8626_, 0, v_log_8604_);
lean_ctor_set(v_reuseFailAlloc_8626_, 1, v___x_8621_);
lean_ctor_set(v_reuseFailAlloc_8626_, 2, v_buildTime_8608_);
lean_ctor_set_uint8(v_reuseFailAlloc_8626_, sizeof(void*)*3, v_action_8605_);
lean_ctor_set_uint8(v_reuseFailAlloc_8626_, sizeof(void*)*3 + 1, v_wantsRebuild_8606_);
v___x_8623_ = v_reuseFailAlloc_8626_;
goto v_reusejp_8622_;
}
v_reusejp_8622_:
{
lean_object* v___x_8624_; lean_object* v___x_8625_; 
v___x_8624_ = l_Array_append___redArg(v_weakArgs_8590_, v_traceArgs_8589_);
lean_dec_ref(v_traceArgs_8589_);
v___x_8625_ = l_Lake_buildLeanExeSync(v_exeFile_8591_, v_objs_8592_, v_libs_8594_, v___x_8624_, v_sharedLean_8593_, v___y_8595_, v___y_8596_, v___y_8597_, v___y_8598_, v___y_8599_, v___x_8623_);
return v___x_8625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_traceArgs_8639_, lean_object* v_weakArgs_8640_, lean_object* v_exeFile_8641_, lean_object* v_objs_8642_, lean_object* v_sharedLean_8643_, lean_object* v_libs_8644_, lean_object* v___y_8645_, lean_object* v___y_8646_, lean_object* v___y_8647_, lean_object* v___y_8648_, lean_object* v___y_8649_, lean_object* v___y_8650_, lean_object* v___y_8651_){
_start:
{
uint8_t v_sharedLean_boxed_8652_; lean_object* v_res_8653_; 
v_sharedLean_boxed_8652_ = lean_unbox(v_sharedLean_8643_);
v_res_8653_ = l_Lake_buildLeanExe___lam__0(v_traceArgs_8639_, v_weakArgs_8640_, v_exeFile_8641_, v_objs_8642_, v_sharedLean_boxed_8652_, v_libs_8644_, v___y_8645_, v___y_8646_, v___y_8647_, v___y_8648_, v___y_8649_, v___y_8650_);
lean_dec_ref(v___y_8649_);
lean_dec(v___y_8648_);
lean_dec(v___y_8647_);
lean_dec(v___y_8646_);
return v_res_8653_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_traceArgs_8654_, lean_object* v_weakArgs_8655_, lean_object* v_exeFile_8656_, uint8_t v_sharedLean_8657_, lean_object* v_linkLibs_8658_, lean_object* v___x_8659_, lean_object* v_objs_8660_, lean_object* v___y_8661_, lean_object* v___y_8662_, lean_object* v___y_8663_, lean_object* v___y_8664_, lean_object* v___y_8665_, lean_object* v___y_8666_){
_start:
{
lean_object* v_trace_8668_; lean_object* v___x_8669_; lean_object* v___f_8670_; lean_object* v___x_8671_; lean_object* v___x_8672_; lean_object* v___x_8673_; uint8_t v___x_8674_; lean_object* v___x_8675_; lean_object* v___x_8676_; 
v_trace_8668_ = lean_ctor_get(v___y_8666_, 1);
v___x_8669_ = lean_box(v_sharedLean_8657_);
v___f_8670_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 5);
lean_closure_set(v___f_8670_, 0, v_traceArgs_8654_);
lean_closure_set(v___f_8670_, 1, v_weakArgs_8655_);
lean_closure_set(v___f_8670_, 2, v_exeFile_8656_);
lean_closure_set(v___f_8670_, 3, v_objs_8660_);
lean_closure_set(v___f_8670_, 4, v___x_8669_);
v___x_8671_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8672_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8658_, v___x_8671_);
v___x_8673_ = lean_unsigned_to_nat(0u);
v___x_8674_ = 0;
v___x_8675_ = l_Lake_Job_mapM___redArg(v___x_8659_, v___x_8672_, v___f_8670_, v___x_8673_, v___x_8674_, v___y_8661_, v___y_8662_, v___y_8663_, v___y_8664_, v___y_8665_, v_trace_8668_);
v___x_8676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8676_, 0, v___x_8675_);
lean_ctor_set(v___x_8676_, 1, v___y_8666_);
return v___x_8676_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_traceArgs_8677_, lean_object* v_weakArgs_8678_, lean_object* v_exeFile_8679_, lean_object* v_sharedLean_8680_, lean_object* v_linkLibs_8681_, lean_object* v___x_8682_, lean_object* v_objs_8683_, lean_object* v___y_8684_, lean_object* v___y_8685_, lean_object* v___y_8686_, lean_object* v___y_8687_, lean_object* v___y_8688_, lean_object* v___y_8689_, lean_object* v___y_8690_){
_start:
{
uint8_t v_sharedLean_boxed_8691_; lean_object* v_res_8692_; 
v_sharedLean_boxed_8691_ = lean_unbox(v_sharedLean_8680_);
v_res_8692_ = l_Lake_buildLeanExe___lam__1(v_traceArgs_8677_, v_weakArgs_8678_, v_exeFile_8679_, v_sharedLean_boxed_8691_, v_linkLibs_8681_, v___x_8682_, v_objs_8683_, v___y_8684_, v___y_8685_, v___y_8686_, v___y_8687_, v___y_8688_, v___y_8689_);
lean_dec_ref(v___y_8688_);
lean_dec(v___y_8687_);
lean_dec(v___y_8686_);
lean_dec(v___y_8685_);
lean_dec_ref(v_linkLibs_8681_);
return v_res_8692_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8693_, lean_object* v_linkObjs_8694_, lean_object* v_linkLibs_8695_, lean_object* v_weakArgs_8696_, lean_object* v_traceArgs_8697_, uint8_t v_sharedLean_8698_, lean_object* v_a_8699_, lean_object* v_a_8700_, lean_object* v_a_8701_, lean_object* v_a_8702_, lean_object* v_a_8703_, lean_object* v_a_8704_){
_start:
{
lean_object* v___x_8706_; lean_object* v___x_8707_; lean_object* v___f_8708_; lean_object* v___x_8709_; lean_object* v___x_8710_; lean_object* v___x_8711_; uint8_t v___x_8712_; lean_object* v___x_8713_; 
v___x_8706_ = l_Lake_instDataKindFilePath;
v___x_8707_ = lean_box(v_sharedLean_8698_);
v___f_8708_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 14, 6);
lean_closure_set(v___f_8708_, 0, v_traceArgs_8697_);
lean_closure_set(v___f_8708_, 1, v_weakArgs_8696_);
lean_closure_set(v___f_8708_, 2, v_exeFile_8693_);
lean_closure_set(v___f_8708_, 3, v___x_8707_);
lean_closure_set(v___f_8708_, 4, v_linkLibs_8695_);
lean_closure_set(v___f_8708_, 5, v___x_8706_);
v___x_8709_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8710_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8694_, v___x_8709_);
v___x_8711_ = lean_unsigned_to_nat(0u);
v___x_8712_ = 1;
v___x_8713_ = l_Lake_Job_bindM___redArg(v___x_8706_, v___x_8710_, v___f_8708_, v___x_8711_, v___x_8712_, v_a_8699_, v_a_8700_, v_a_8701_, v_a_8702_, v_a_8703_, v_a_8704_);
return v___x_8713_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8714_, lean_object* v_linkObjs_8715_, lean_object* v_linkLibs_8716_, lean_object* v_weakArgs_8717_, lean_object* v_traceArgs_8718_, lean_object* v_sharedLean_8719_, lean_object* v_a_8720_, lean_object* v_a_8721_, lean_object* v_a_8722_, lean_object* v_a_8723_, lean_object* v_a_8724_, lean_object* v_a_8725_, lean_object* v_a_8726_){
_start:
{
uint8_t v_sharedLean_boxed_8727_; lean_object* v_res_8728_; 
v_sharedLean_boxed_8727_ = lean_unbox(v_sharedLean_8719_);
v_res_8728_ = l_Lake_buildLeanExe(v_exeFile_8714_, v_linkObjs_8715_, v_linkLibs_8716_, v_weakArgs_8717_, v_traceArgs_8718_, v_sharedLean_boxed_8727_, v_a_8720_, v_a_8721_, v_a_8722_, v_a_8723_, v_a_8724_, v_a_8725_);
lean_dec_ref(v_a_8725_);
lean_dec_ref(v_a_8724_);
lean_dec(v_a_8723_);
lean_dec(v_a_8722_);
lean_dec(v_a_8721_);
lean_dec_ref(v_linkObjs_8715_);
return v_res_8728_;
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
