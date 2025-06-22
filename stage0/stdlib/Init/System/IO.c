// Lean compiler output
// Module: Init.System.IO
// Imports: Init.System.IOError Init.System.FilePath Init.System.ST Init.Data.Ord Init.Data.String.Extra
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
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__35____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__0;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_termPrintln_x21_______closed__9;
static lean_object* l_instOrElseEIO___closed__0;
static lean_object* l___auto___closed__9____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedSystemTime___closed__1;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
static lean_object* l_instMonadEIO___closed__2;
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_termPrintln_x21____;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instOrElseEIO___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__1(size_t, lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_;
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3;
static lean_object* l_instMonadEIO___closed__6;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
static lean_object* l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_;
LEAN_EXPORT lean_object* l_IO_println(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_check_canceled(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_;
lean_object* lean_io_get_tid(lean_object*);
static lean_object* l___auto___closed__33____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__20____x40_Init_System_IO___hyg_1906_;
lean_object* lean_io_create_tempdir(lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l___auto___closed__4____x40_Init_System_IO___hyg_1906_;
static lean_object* l_termPrintln_x21_______closed__8;
static lean_object* l___auto___closed__13____x40_Init_System_IO___hyg_1906_;
static lean_object* l_IO_FS_instReprFileType___closed__0;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_IO_reprTaskState____x40_Init_System_IO___hyg_1435____boxed(lean_object*, lean_object*);
static lean_object* l_IO_println___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___closed__0;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
static lean_object* l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_;
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_;
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085____boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__0;
LEAN_EXPORT lean_object* l_IO_ordTaskState____x40_Init_System_IO___hyg_1650____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime;
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*, lean_object*);
static lean_object* l_IO_FS_lines___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__5___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__1;
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t, uint8_t);
static lean_object* l_termPrintln_x21_______closed__1;
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO;
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_cancel_token_is_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___auto___closed__38____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_;
lean_object* lean_io_remove_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
static lean_object* l_termPrintln_x21_______closed__13;
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
static lean_object* l_termPrintln_x21_______closed__3;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
static lean_object* l___auto___closed__7____x40_Init_System_IO___hyg_1906_;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_;
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO;
static lean_object* l_IO_Process_run___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__0;
static lean_object* l_IO_FS_readBinFile___closed__0;
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_;
lean_object* l_ByteArray_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__0(lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346_(lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___auto___closed__23____x40_Init_System_IO___hyg_1906_;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream;
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_System_IO___hyg_1906_;
lean_object* lean_get_stdout(lean_object*);
static lean_object* l_termPrintln_x21_______closed__4;
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085____boxed(lean_object*);
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instReprTaskState;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__37____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_reprTaskState____x40_Init_System_IO___hyg_1435_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
static lean_object* l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState;
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_;
static lean_object* l_IO_FS_Mode_noConfusion___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_instToStringTaskState___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___auto___closed__10____x40_Init_System_IO___hyg_1906_;
static lean_object* l___auto___closed__11____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___auto___closed__17____x40_Init_System_IO___hyg_1906_;
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_;
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Process_output___closed__0;
LEAN_EXPORT lean_object* l_IO_instLTTaskState;
static lean_object* l___auto___closed__6____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__1;
static lean_object* l___auto___closed__16____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMinTaskState;
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346_(lean_object*, lean_object*);
static lean_object* l___auto___closed__39____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadFinallyEIO___closed__0;
static lean_object* l_IO_FS_withTempDir___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_ordTaskState____x40_Init_System_IO___hyg_1650_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217____boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_;
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__0;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
static lean_object* l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_;
LEAN_EXPORT lean_object* l_IO_appDir(lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___auto___closed__3____x40_Init_System_IO___hyg_1906_;
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0;
lean_object* lean_get_stdin(lean_object*);
static lean_object* l_IO_FS_Handle_readBinToEnd___closed__0;
static lean_object* l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_;
static lean_object* l___auto___closed__24____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime;
static lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
lean_object* lean_io_prim_handle_is_tty(lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__3(lean_object*);
lean_object* lean_get_stderr(lean_object*);
static lean_object* l_IO_instReprTaskState___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143____boxed(lean_object*, lean_object*);
static lean_object* l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_;
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_multi_threaded(lean_object*, lean_object*);
static lean_object* l_IO_FS_readFile___closed__0;
static lean_object* l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static lean_object* l___auto___closed__31____x40_Init_System_IO___hyg_1906_;
static lean_object* l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_;
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_create_tempfile(lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object*);
lean_object* l_EStateM_instMonadExceptOfOfBacktrackable___redArg(lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry___redArg____x40_Init_System_IO___hyg_2816_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry___closed__0;
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_;
lean_object* lean_task_get_own(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Init_System_IO___hyg_1906_;
static lean_object* l_IO_FS_readFile___closed__1;
static lean_object* l_instMonadEIO___closed__1;
static lean_object* l___auto___closed__2____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object*, lean_object*);
static lean_object* l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_;
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_;
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry;
LEAN_EXPORT lean_object* l_IO_instToStringTaskState;
lean_object* lean_io_process_set_current_dir(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_;
static lean_object* l_IO_FS_instReprMetadata___closed__0;
static lean_object* l___auto___closed__27____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042____boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_withTempFile___redArg___closed__0;
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__8;
static lean_object* l___auto___closed__8____x40_Init_System_IO___hyg_1906_;
static lean_object* l_termPrintln_x21_______closed__12;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
static lean_object* l___auto___closed__36____x40_Init_System_IO___hyg_1906_;
static lean_object* l___auto___closed__40____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
static lean_object* l___auto___closed__42____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__15;
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_instMonadEIO___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__5;
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346____boxed(lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__22____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__2;
uint32_t lean_io_process_child_pid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_;
static lean_object* l_termPrintln_x21_______closed__16;
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l_instMonadEIO___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
LEAN_EXPORT uint8_t l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__4___boxed(lean_object*, lean_object*);
static lean_object* l_IO_withStdout___redArg___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894____boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType;
lean_object* lean_io_app_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__1;
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object*);
static lean_object* l___auto___closed__19____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
static lean_object* l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_;
static lean_object* l___auto___closed__26____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__10;
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__2;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
static lean_object* l_IO_FS_instInhabitedStream___lam__0___closed__1;
static lean_object* l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_;
lean_object* lean_chmod(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto___closed__30____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType;
LEAN_EXPORT lean_object* l_IO_instMaxTaskState;
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__25____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
static lean_object* l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
static lean_object* l_termPrintln_x21_______closed__14;
LEAN_EXPORT lean_object* l_IO_instOrdTaskState;
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
static lean_object* l_instMonadEIO___closed__9;
static lean_object* l_instOrElseEIO___closed__1;
static lean_object* l___auto___closed__29____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346____boxed(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1;
static lean_object* l___auto___closed__12____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__32____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Init_System_IO___hyg_1906_;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2;
static lean_object* l_IO_TaskState_toString___closed__2;
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
lean_object* lean_io_initializing(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*, lean_object*);
lean_object* l_EStateM_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instLETaskState;
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Handle_readToEnd___closed__1;
static lean_object* l___auto___closed__41____x40_Init_System_IO___hyg_1906_;
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143_(lean_object*, lean_object*);
static lean_object* l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_IO_FS_instInhabitedStream___lam__0___closed__0;
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
static lean_object* l_IO_FS_instBEqFileType___closed__0;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
static lean_object* l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__5(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_TaskState_toString___closed__0;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instOrdSystemTime___closed__0;
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__11;
static lean_object* l_IO_instOrdTaskState___closed__0;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
static lean_object* l___auto___closed__18____x40_Init_System_IO___hyg_1906_;
static lean_object* l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_;
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
static lean_object* l_termPrintln_x21_______closed__0;
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Init_System_IO___hyg_1906_;
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object*);
static uint32_t l_IO_FS_instInhabitedSystemTime___closed__0;
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
static lean_object* l_IO_FS_instBEqSystemTime___closed__0;
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__34____x40_Init_System_IO___hyg_1906_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___auto___closed__28____x40_Init_System_IO___hyg_1906_;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_get_pid(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__6;
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_;
static lean_object* l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_object* lean_io_process_child_kill(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__0;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Handle_readToEnd___closed__0;
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__5;
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l_termPrintln_x21_______closed__7;
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadBaseIO___closed__0;
LEAN_EXPORT uint8_t l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(uint8_t, uint8_t);
static lean_object* l_IO_TaskState_toString___closed__1;
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_get_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
static lean_object* l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instMonadEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__0), 5, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_map), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadEIO___closed__0;
x_2 = l_instMonadEIO___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instMonadEIO___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instMonadEIO___closed__6;
x_2 = l_instMonadEIO___closed__2;
x_3 = l_instMonadEIO___closed__1;
x_4 = l_instMonadEIO___closed__5;
x_5 = l_instMonadEIO___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_instMonadEIO___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadEIO___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadEIO___closed__8;
x_2 = l_instMonadEIO___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadEIO___closed__9;
return x_2;
}
}
static lean_object* _init_l_instMonadFinallyEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonadFinally___lam__0), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadFinallyEIO___closed__0;
return x_2;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_nonBacktrackable(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadExceptOfEIO___closed__0;
x_2 = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadExceptOfEIO___closed__1;
return x_2;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadExceptOfEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instOrElseEIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instOrElseEIO___closed__0;
x_2 = l_instMonadExceptOfMonadExceptOf___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_instOrElseEIO___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instOrElseEIO___closed__1;
x_2 = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
lean_closure_set(x_2, 3, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instOrElseEIO___closed__2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_instMonadBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadBaseIO___closed__0;
return x_1;
}
}
static lean_object* _init_l_instMonadFinallyBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadFinallyEIO___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_1(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_ofExcept___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_ofExcept___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_ofExcept(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_apply_1(x_3, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_apply_1(x_3, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_apply_1(x_3, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_apply_1(x_3, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_unsafeBaseIO___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
x_3 = l_unsafeBaseIO___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
x_5 = l_unsafeBaseIO___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
x_3 = l_unsafeBaseIO___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
x_4 = l_unsafeBaseIO___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_timeit(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_allocprof(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_initializing(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_as_task(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_io_map_task(x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_io_bind_task(x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_map_task(x_2, x_1, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BaseIO_chainTask___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_BaseIO_chainTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_BaseIO_chainTask(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = l_List_reverse___redArg(x_5);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_9 = l_BaseIO_mapTasks_go___redArg(x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (x_3 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_List_reverse___redArg(x_5);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_io_as_task(x_8, x_2, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
x_10 = l_List_reverse___redArg(x_5);
x_11 = lean_apply_2(x_1, x_10, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_task_pure(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_task_pure(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___redArg___lam__0), 4, 2);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_1);
x_22 = lean_io_map_task(x_21, x_20, x_2, x_3, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_box(x_3);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_19);
x_26 = lean_io_bind_task(x_23, x_25, x_2, x_3, x_6);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_BaseIO_mapTasks_go___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_BaseIO_mapTasks_go___redArg___lam__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_BaseIO_mapTasks_go___redArg(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_BaseIO_mapTasks_go(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_BaseIO_mapTasks_go___redArg(x_1, x_3, x_4, x_2, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_BaseIO_mapTasks___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_BaseIO_mapTasks___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_BaseIO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
x_7 = lean_io_as_task(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_io_map_task(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_io_map_task(x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EIO_mapTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_EIO_mapTask(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_task_pure(x_11);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_task_pure(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_bind_task(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = lean_io_bind_task(x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EIO_bindTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_EIO_bindTask(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_map_task(x_6, x_1, x_3, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_EIO_chainTask___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EIO_chainTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_EIO_chainTask(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_BaseIO_mapTasks___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = l_BaseIO_mapTasks___redArg(x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EIO_mapTasks___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_EIO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set_tag(x_2, 18);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_ofExcept___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_lazyPure___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_ms_now(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_nanos_now(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_io_get_random_bytes(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_dbg_sleep(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_sleep___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_IO_sleep(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_2);
x_6 = lean_io_as_task(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_io_map_task(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_io_map_task(x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_mapTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_IO_mapTask(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_task_pure(x_11);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_task_pure(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_bind_task(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = lean_io_bind_task(x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_bindTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_IO_bindTask(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_chainTask___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_EIO_chainTask___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_chainTask___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_IO_chainTask(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_BaseIO_mapTasks___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = l_BaseIO_mapTasks___redArg(x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_mapTasks___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_IO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_check_canceled(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_cancel(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_TaskState_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_TaskState_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_TaskState_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_TaskState_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_TaskState_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.waiting", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.running", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.finished", 21, 21);
return x_1;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_reprTaskState____x40_Init_System_IO___hyg_1435_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; 
switch (x_1) {
case 0:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_3 = x_29;
goto block_10;
}
else
{
lean_object* x_30; 
x_30 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_3 = x_30;
goto block_10;
}
}
case 1:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_11 = x_33;
goto block_18;
}
else
{
lean_object* x_34; 
x_34 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_11 = x_34;
goto block_18;
}
}
default: 
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_19 = x_37;
goto block_26;
}
else
{
lean_object* x_38; 
x_38 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_19 = x_38;
goto block_26;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_IO_reprTaskState____x40_Init_System_IO___hyg_1435____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_IO_reprTaskState____x40_Init_System_IO___hyg_1435_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_instReprTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_reprTaskState____x40_Init_System_IO___hyg_1435____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instReprTaskState() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instReprTaskState___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_1, x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_IO_TaskState_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_IO_TaskState_toCtorIdx(x_1);
x_4 = l_IO_TaskState_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_instDecidableEqTaskState(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_IO_ordTaskState____x40_Init_System_IO___hyg_1650_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
switch (x_2) {
case 0:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(2);
x_9 = lean_unbox(x_8);
return x_9;
}
case 1:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
}
default: 
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
default: 
{
lean_object* x_14; 
x_14 = lean_box(x_2);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_17 = lean_box(2);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ordTaskState____x40_Init_System_IO___hyg_1650____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_ordTaskState____x40_Init_System_IO___hyg_1650_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_instOrdTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_ordTaskState____x40_Init_System_IO___hyg_1650____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instOrdTaskState() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instOrdTaskState___closed__0;
return x_1;
}
}
static lean_object* _init_l_IO_instLTTaskState() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_instLETaskState() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_ordTaskState____x40_Init_System_IO___hyg_1650_(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 2)
{
return x_2;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
static lean_object* _init_l_IO_instMinTaskState() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMinTaskState___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_instMinTaskState___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_ordTaskState____x40_Init_System_IO___hyg_1650_(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 2)
{
return x_1;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
static lean_object* _init_l_IO_instMaxTaskState() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMaxTaskState___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_instMaxTaskState___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_TaskState_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("waiting", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_TaskState_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("running", 7, 7);
return x_1;
}
}
static lean_object* _init_l_IO_TaskState_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("finished", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_toString___closed__0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_IO_TaskState_toString___closed__1;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_IO_TaskState_toString___closed__2;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_TaskState_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_instToStringTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_TaskState_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instToStringTaskState() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instToStringTaskState___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_get_task_state(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_io_get_task_state(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_io_get_task_state(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_box(1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_hasFinished___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_hasFinished(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto___closed__0____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__2____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__2____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Init_System_IO___hyg_1906_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__10____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__2____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__12____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10____x40_Init_System_IO___hyg_1906_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__13____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__12____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__14____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l___auto___closed__16____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__15____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__14____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__17____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.zero_lt_succ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___auto___closed__18____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__17____x40_Init_System_IO___hyg_1906_;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__19____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__18____x40_Init_System_IO___hyg_1906_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___auto___closed__17____x40_Init_System_IO___hyg_1906_;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__20____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___auto___closed__21____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero_lt_succ", 12, 12);
return x_1;
}
}
static lean_object* _init_l___auto___closed__22____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__21____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__20____x40_Init_System_IO___hyg_1906_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__23____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l___auto___closed__22____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__19____x40_Init_System_IO___hyg_1906_;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__24____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__23____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__25____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__26____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__25____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__14____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__27____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l___auto___closed__28____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__27____x40_Init_System_IO___hyg_1906_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__29____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__28____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__30____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__29____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__26____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__31____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__30____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__32____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__31____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__9____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__33____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__32____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__24____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__34____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__33____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__16____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__35____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__34____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__13____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__36____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__35____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__11____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__37____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__36____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__38____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__37____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__9____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__39____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__38____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__40____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__39____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__7____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__41____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__40____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__5____x40_Init_System_IO___hyg_1906_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__42____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__41____x40_Init_System_IO___hyg_1906_;
x_2 = l___auto___closed__4____x40_Init_System_IO___hyg_1906_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1906_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__42____x40_Init_System_IO___hyg_1906_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_wait_any(x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_get_num_heartbeats(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_set_heartbeats(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_io_get_num_heartbeats(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_add(x_4, x_1);
lean_dec(x_4);
x_7 = lean_io_set_heartbeats(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_addHeartbeats(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_FS_Mode_toCtorIdx(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Mode_noConfusion___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_TaskState_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Mode_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Mode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Mode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_Mode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instInhabitedStream___lam__0___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream___lam__0___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__1(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream___lam__0___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lam__1___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lam__2___boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lam__3), 1, 0);
x_5 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lam__4___boxed), 2, 0);
x_6 = l_IO_FS_instInhabitedStream___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_instInhabitedStream___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream___lam__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream___lam__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stderr(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdin(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdout(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stderr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_1 = x_7;
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_iterate___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_lock(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_try_lock(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_unlock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_tty(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_rewind(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_truncate(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_file(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_create_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_rename(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_create_tempfile(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_create_tempdir(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_prim_handle_mk(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_prim_handle_mk(x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_withFile___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_withFile(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 10;
x_5 = lean_string_push(x_2, x_4);
x_6 = lean_io_prim_handle_put_str(x_1, x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_putStrLn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = 1024;
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_ByteArray_isEmpty(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_5);
x_10 = l_ByteArray_append(x_2, x_7);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_ByteArray_isEmpty(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_ByteArray_append(x_2, x_12);
lean_dec(x_12);
x_2 = x_15;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEndInto_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEndInto_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEndInto(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_IO_FS_Handle_readBinToEnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_Handle_readBinToEnd___closed__0;
x_4 = l_IO_FS_Handle_readBinToEndInto_loop(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readBinToEnd(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Handle_readToEnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tried to read from handle containing non UTF-8 data.", 52, 52);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Handle_readToEnd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Handle_readToEnd___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readBinToEnd(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_string_validate_utf8(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l_IO_FS_Handle_readToEnd___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
x_8 = lean_string_from_utf8_unchecked(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_string_validate_utf8(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = l_IO_FS_Handle_readToEnd___closed__1;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_from_utf8_unchecked(x_9);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines_read(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_get_line(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_12 = lean_string_length(x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; 
x_15 = lean_string_utf8_byte_size(x_6);
x_16 = lean_string_utf8_prev(x_6, x_15);
x_17 = lean_string_utf8_get(x_6, x_16);
lean_dec(x_16);
x_18 = 10;
x_19 = lean_uint32_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_array_push(x_2, x_6);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
lean_free_object(x_4);
x_21 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
lean_inc(x_6);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_15);
x_23 = l_Substring_prevn(x_22, x_21, x_15);
lean_dec(x_22);
x_24 = lean_string_utf8_extract(x_6, x_13, x_23);
lean_dec(x_23);
lean_dec(x_6);
x_25 = lean_string_utf8_byte_size(x_24);
x_26 = lean_string_utf8_prev(x_24, x_25);
x_27 = lean_string_utf8_get(x_24, x_26);
lean_dec(x_26);
x_28 = 13;
x_29 = lean_uint32_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_25);
x_8 = x_24;
goto block_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_25);
lean_inc(x_24);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_25);
x_31 = l_Substring_prevn(x_30, x_21, x_25);
lean_dec(x_30);
x_32 = lean_string_utf8_extract(x_24, x_13, x_31);
lean_dec(x_31);
lean_dec(x_24);
x_8 = x_32;
goto block_11;
}
}
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
block_11:
{
lean_object* x_9; 
x_9 = lean_array_push(x_2, x_8);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_39 = lean_string_length(x_33);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint32_t x_44; uint32_t x_45; uint8_t x_46; 
x_42 = lean_string_utf8_byte_size(x_33);
x_43 = lean_string_utf8_prev(x_33, x_42);
x_44 = lean_string_utf8_get(x_33, x_43);
lean_dec(x_43);
x_45 = 10;
x_46 = lean_uint32_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
x_47 = lean_array_push(x_2, x_33);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; uint32_t x_56; uint8_t x_57; 
x_49 = lean_unsigned_to_nat(1u);
lean_inc(x_42);
lean_inc(x_33);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_42);
x_51 = l_Substring_prevn(x_50, x_49, x_42);
lean_dec(x_50);
x_52 = lean_string_utf8_extract(x_33, x_40, x_51);
lean_dec(x_51);
lean_dec(x_33);
x_53 = lean_string_utf8_byte_size(x_52);
x_54 = lean_string_utf8_prev(x_52, x_53);
x_55 = lean_string_utf8_get(x_52, x_54);
lean_dec(x_54);
x_56 = 13;
x_57 = lean_uint32_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_dec(x_53);
x_35 = x_52;
goto block_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_53);
lean_inc(x_52);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_53);
x_59 = l_Substring_prevn(x_58, x_49, x_53);
lean_dec(x_58);
x_60 = lean_string_utf8_extract(x_52, x_40, x_59);
lean_dec(x_59);
lean_dec(x_52);
x_35 = x_60;
goto block_38;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_33);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_34);
return x_61;
}
block_38:
{
lean_object* x_36; 
x_36 = lean_array_push(x_2, x_35);
x_2 = x_36;
x_3 = x_34;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_4);
if (x_62 == 0)
{
return x_4;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_4, 0);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_4);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_lines_read(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_IO_FS_lines___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_lines___closed__0;
x_9 = l_IO_FS_lines_read(x_6, x_8, x_7);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_lines(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_write(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeBinFile(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_put_str(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 10;
x_6 = lean_string_push(x_2, x_5);
x_7 = lean_apply_2(x_4, x_6, x_3);
return x_7;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("root", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_2 = l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fileName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry___redArg____x40_Init_System_IO___hyg_2816_(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_6 = l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_;
x_7 = l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_;
x_10 = l_String_quote(x_3);
lean_dec(x_3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_12 = l_Repr_addAppParen(x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_;
x_26 = l_String_quote(x_4);
lean_dec(x_4);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_33 = l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_14);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_42 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_43 = l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_;
x_44 = l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_;
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_;
x_47 = l_String_quote(x_40);
lean_dec(x_40);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Repr_addAppParen(x_49, x_45);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_42);
x_63 = l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_;
x_64 = l_String_quote(x_41);
lean_dec(x_41);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_unbox(x_52);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_68);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_71 = l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_;
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_;
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_unbox(x_52);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_77);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprDirEntry___redArg____x40_Init_System_IO___hyg_2816_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2816____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprDirEntry___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_FS_FileType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Mode_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_FileType_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_FileType_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_FileType_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.dir", 18, 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.file", 19, 19);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.symlink", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.other", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; lean_object* x_27; 
switch (x_1) {
case 0:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_3 = x_37;
goto block_10;
}
else
{
lean_object* x_38; 
x_38 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_3 = x_38;
goto block_10;
}
}
case 1:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_42; 
x_42 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_11 = x_42;
goto block_18;
}
}
case 2:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_19 = x_45;
goto block_26;
}
else
{
lean_object* x_46; 
x_46 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_19 = x_46;
goto block_26;
}
}
default: 
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1024u);
x_48 = lean_nat_dec_le(x_47, x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_27 = x_49;
goto block_34;
}
else
{
lean_object* x_50; 
x_50 = l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_;
x_27 = x_50;
goto block_34;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_2);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instReprFileType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprFileType___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_IO_FS_FileType_toCtorIdx(x_1);
x_4 = l_IO_FS_FileType_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqFileType___closed__0;
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_2 = l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nsec", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_4 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_5 = l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_;
x_6 = l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_;
x_39 = lean_int_dec_lt(x_2, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Int_repr(x_2);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_7 = x_41;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Int_repr(x_2);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Repr_addAppParen(x_43, x_37);
x_7 = x_44;
goto block_36;
}
block_36:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_;
x_21 = lean_uint32_to_nat(x_3);
x_22 = l_Nat_reprFast(x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unbox(x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_29 = l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_9);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_reprSystemTime____x40_Init_System_IO___hyg_3085____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprSystemTime___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_uint32_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3143____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqSystemTime___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
x_7 = lean_int_dec_lt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_int_dec_eq(x_3, x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_uint32_dec_lt(x_4, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_uint32_dec_eq(x_4, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3217____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instOrdSystemTime___closed__0;
return x_1;
}
}
static uint32_t _init_l_IO_FS_instInhabitedSystemTime___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__0;
x_2 = l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("accessed", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_2 = l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("modified", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("byteSize", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_6 = l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_;
x_7 = l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_;
x_8 = l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3085_(x_3);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unbox(x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_30 = l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_uint64_to_nat(x_4);
x_34 = l_Nat_reprFast(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_unbox(x_12);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_18);
x_42 = l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_;
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_6);
x_45 = l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_;
x_46 = l_IO_FS_reprFileType____x40_Init_System_IO___hyg_2894_(x_5, x_9);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_12);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_;
x_52 = l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_;
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
x_54 = l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_;
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_unbox(x_12);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
return x_57;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_reprMetadata___redArg____x40_Init_System_IO___hyg_3346_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_reprMetadata____x40_Init_System_IO___hyg_3346____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprMetadata___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_symlink_metadata(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 8);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(x_6, x_8);
x_10 = lean_box(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 8);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(x_13, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(1);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
x_20 = lean_array_uget(x_4, x_6);
x_21 = l_IO_FS_DirEntry_path(x_20);
lean_inc(x_21);
x_22 = lean_array_push(x_8, x_21);
x_23 = lean_io_metadata(x_21, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 8);
lean_dec(x_24);
x_26 = lean_box(x_25);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_1);
x_28 = l_System_FilePath_walkDir_go(x_1, x_21, x_22, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_31;
x_12 = x_30;
goto block_16;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
case 2:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_io_realpath(x_21, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_System_FilePath_isDir(x_34, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_34);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_22;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
lean_inc(x_1);
lean_inc(x_3);
x_41 = lean_apply_2(x_1, x_3, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_34);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_22;
x_12 = x_44;
goto block_16;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
lean_inc(x_1);
x_46 = l_System_FilePath_walkDir_go(x_1, x_34, x_22, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_49;
x_12 = x_48;
goto block_16;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_33);
if (x_54 == 0)
{
return x_33;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_33, 0);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_33);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
default: 
{
lean_object* x_58; 
lean_dec(x_26);
lean_dec(x_21);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_22;
x_12 = x_58;
goto block_16;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_21);
x_59 = lean_ctor_get(x_23, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 11)
{
lean_object* x_60; 
lean_dec(x_59);
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_dec(x_23);
lean_inc(x_2);
x_10 = x_2;
x_11 = x_22;
x_12 = x_60;
goto block_16;
}
else
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_23, 0);
lean_dec(x_62);
return x_23;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_10;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_5 = lean_apply_2(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_io_read_dir(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_size(x_18);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0(x_1, x_20, x_2, x_18, x_21, x_22, x_20, x_3, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_20);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
return x_23;
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
return x_5;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___System_FilePath_walkDir_go_spec__0(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_lines___closed__0;
x_5 = l_System_FilePath_walkDir_go(x_2, x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_byte_array(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_io_prim_handle_mk(x_1, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 0;
x_14 = lean_usize_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_IO_FS_readBinFile___closed__0;
x_16 = l_IO_FS_Handle_readBinToEndInto_loop(x_9, x_15, x_10);
lean_dec(x_9);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_io_prim_handle_read(x_9, x_12, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_IO_FS_Handle_readBinToEndInto_loop(x_9, x_18, x_19);
lean_dec(x_9);
return x_20;
}
else
{
lean_dec(x_9);
return x_17;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_readFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tried to read file '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_readFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' containing non UTF-8 data.", 28, 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_string_validate_utf8(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_7 = l_IO_FS_readFile___closed__0;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_IO_FS_readFile___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; 
x_12 = lean_string_from_utf8_unchecked(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_string_validate_utf8(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_16 = l_IO_FS_readFile___closed__0;
x_17 = lean_string_append(x_16, x_1);
x_18 = l_IO_FS_readFile___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_string_from_utf8_unchecked(x_13);
lean_dec(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__0___boxed), 1, 0);
x_10 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_10, 0, x_4);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_withStdin___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_withStdin___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_withStdin___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_14);
return x_15;
}
}
static lean_object* _init_l_IO_withStdout___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_withStdout___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_10, 0, x_4);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_withStdout___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_withStdout___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_10, 0, x_4);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_withStderr___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_get_stdout(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_apply_2(x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_print___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO_println___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_println___redArg___closed__0;
x_5 = lean_apply_1(x_1, x_2);
x_6 = 10;
x_7 = lean_string_push(x_5, x_6);
x_8 = l_IO_print___redArg(x_4, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_println___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_get_stderr(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_apply_2(x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprint___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_println___redArg___closed__0;
x_5 = lean_apply_1(x_1, x_2);
x_6 = 10;
x_7 = lean_string_push(x_5, x_6);
x_8 = l_IO_eprint___redArg(x_4, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprintln___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stderr(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_appDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.appDir: unexpected filename '", 32, 32);
return x_1;
}
}
static lean_object* _init_l_IO_appDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_System_FilePath_parent(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_appDir___closed__0;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = l_IO_appDir___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_4);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_io_realpath(x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_System_FilePath_parent(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_IO_appDir___closed__0;
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_IO_appDir___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_io_realpath(x_23, x_15);
return x_24;
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_System_FilePath_isDir(x_1, x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_25) == 0)
{
x_3 = x_24;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_IO_FS_createDirAll(x_26, x_24);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_3 = x_28;
goto block_20;
}
else
{
return x_27;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
block_20:
{
lean_object* x_4; 
x_4 = lean_io_create_dir(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_System_FilePath_isDir(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_createDirAll(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = l_IO_FS_DirEntry_path(x_15);
x_17 = lean_io_symlink_metadata(x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 8);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_IO_FS_beqFileType____x40_Init_System_IO___hyg_3042_(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_io_remove_file(x_16, x_19);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_7 = x_1;
x_8 = x_25;
goto block_12;
}
else
{
lean_dec(x_1);
return x_24;
}
}
else
{
lean_object* x_26; 
x_26 = l_IO_FS_removeDirAll(x_16, x_19);
lean_dec(x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_1);
x_7 = x_1;
x_8 = x_27;
goto block_12;
}
else
{
lean_dec(x_1);
return x_26;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_array_size(x_4);
x_8 = 0;
x_9 = l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0(x_6, x_4, x_7, x_8, x_6, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_io_remove_dir(x_1, x_10);
return x_11;
}
else
{
return x_9;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___IO_FS_removeDirAll_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_removeDirAll(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_8);
x_10 = lean_apply_2(x_2, x_7, x_8);
x_11 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_apply_2(x_3, lean_box(0), x_11);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_5, x_14);
return x_15;
}
}
static lean_object* _init_l_IO_FS_withTempFile___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_createTempFile___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_withStdout___redArg___closed__0;
x_9 = l_IO_FS_withTempFile___redArg___closed__0;
lean_inc(x_3);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_8);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withTempFile___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_5, x_12);
return x_13;
}
}
static lean_object* _init_l_IO_FS_withTempDir___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_createTempDir___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_withStdout___redArg___closed__0;
x_9 = l_IO_FS_withTempDir___redArg___closed__0;
lean_inc(x_3);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_8);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withTempDir___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_process_get_current_dir(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_set_current_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_process_get_pid(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_Process_Stdio_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Mode_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Process_Stdio_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_Process_Stdio_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_Process_Stdio_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_spawn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_try_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_kill(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_take_stdin(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_io_process_child_pid(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_io_error_to_string(x_4);
lean_ctor_set_tag(x_1, 18);
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
static lean_object* _init_l_IO_Process_output___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 0, 3);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 2, x_6);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = l_IO_Process_output___closed__0;
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_unsigned_to_nat(9u);
x_13 = lean_io_as_task(x_11, x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Handle_readToEnd(x_10, x_15);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_io_process_child_wait(x_5, x_7, x_18);
lean_dec(x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_task_get_own(x_14);
x_23 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint32_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_unbox_uint32(x_20);
lean_dec(x_20);
lean_ctor_set_uint32(x_26, sizeof(void*)*2, x_27);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_17);
x_31 = lean_unbox_uint32(x_20);
lean_dec(x_20);
lean_ctor_set_uint32(x_30, sizeof(void*)*2, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_14);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
return x_6;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_ctor_get(x_1, 2);
x_51 = lean_ctor_get(x_1, 3);
x_52 = lean_ctor_get(x_1, 4);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_55 = l_IO_Process_output___closed__0;
x_56 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*5, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*5 + 1, x_54);
x_57 = lean_io_process_spawn(x_56, x_2);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
x_62 = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(x_62, 0, x_60);
x_63 = lean_unsigned_to_nat(9u);
x_64 = lean_io_as_task(x_62, x_63, x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_IO_FS_Handle_readToEnd(x_61, x_66);
lean_dec(x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_io_process_child_wait(x_55, x_58, x_69);
lean_dec(x_58);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_task_get_own(x_65);
x_74 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_73, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint32_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_68);
x_79 = lean_unbox_uint32(x_71);
lean_dec(x_71);
lean_ctor_set_uint32(x_78, sizeof(void*)*2, x_79);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
lean_dec(x_68);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_83 = x_74;
} else {
 lean_dec_ref(x_74);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
lean_dec(x_65);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_87 = x_70;
} else {
 lean_dec_ref(x_70);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_65);
lean_dec(x_58);
x_89 = lean_ctor_get(x_67, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_91 = x_67;
} else {
 lean_dec_ref(x_67);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_57, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_57, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_95 = x_57;
} else {
 lean_dec_ref(x_57);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Process_output___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_Process_run___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("process '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_IO_Process_run___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' exited with code ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_IO_Process_run___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 0;
x_10 = lean_uint32_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_IO_Process_run___closed__0;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_IO_Process_run___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_uint32_to_nat(x_6);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = l_IO_Process_run___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_8);
lean_dec(x_8);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_ctor_get_uint32(x_23, sizeof(void*)*2);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = 0;
x_29 = lean_uint32_dec_eq(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_IO_Process_run___closed__0;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_IO_Process_run___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_uint32_to_nat(x_25);
x_36 = l_Nat_reprFast(x_35);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = l_IO_Process_run___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_27);
lean_dec(x_27);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_24);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_27);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_24);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
return x_3;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_exit(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_get_tid(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; uint32_t x_4; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_16; 
x_8 = lean_ctor_get_uint8(x_1, 0);
x_9 = lean_ctor_get_uint8(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, 2);
if (x_8 == 0)
{
uint32_t x_20; 
x_20 = 0;
x_16 = x_20;
goto block_19;
}
else
{
uint32_t x_21; 
x_21 = 4;
x_16 = x_21;
goto block_19;
}
block_7:
{
uint32_t x_5; uint32_t x_6; 
x_5 = lean_uint32_lor(x_2, x_4);
x_6 = lean_uint32_lor(x_3, x_5);
return x_6;
}
block_15:
{
if (x_10 == 0)
{
uint32_t x_13; 
x_13 = 0;
x_2 = x_12;
x_3 = x_11;
x_4 = x_13;
goto block_7;
}
else
{
uint32_t x_14; 
x_14 = 1;
x_2 = x_12;
x_3 = x_11;
x_4 = x_14;
goto block_7;
}
}
block_19:
{
if (x_9 == 0)
{
uint32_t x_17; 
x_17 = 0;
x_11 = x_16;
x_12 = x_17;
goto block_15;
}
else
{
uint32_t x_18; 
x_18 = 2;
x_11 = x_16;
x_12 = x_18;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_AccessRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint32_t x_5; uint32_t x_6; uint32_t x_7; uint32_t x_8; uint32_t x_9; uint32_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_IO_AccessRight_flags(x_2);
x_6 = 6;
x_7 = lean_uint32_shift_left(x_5, x_6);
x_8 = l_IO_AccessRight_flags(x_3);
x_9 = 3;
x_10 = lean_uint32_shift_left(x_8, x_9);
x_11 = l_IO_AccessRight_flags(x_4);
x_12 = lean_uint32_lor(x_10, x_11);
x_13 = lean_uint32_lor(x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_FileRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_IO_FileRight_flags(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_setAccessRights(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_instMonadLiftSTRealWorldBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_st_mk_ref(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_st_ref_set(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_CancelToken_set(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_ref_get(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_CancelToken_isSet(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_io_cancel_token_is_set(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_ref_get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_byte_array_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_byte_array_fget(x_1, x_2);
x_13 = 0;
x_14 = lean_uint8_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint8_dec_eq(x_12, x_15);
x_3 = x_16;
goto block_8;
}
else
{
x_3 = x_14;
goto block_8;
}
}
block_8:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_usize_to_nat(x_2);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = l_ByteArray_extract(x_8, x_9, x_11);
lean_dec(x_11);
x_13 = lean_byte_array_size(x_12);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_14);
x_15 = lean_st_ref_set(x_1, x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_usize_to_nat(x_2);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_inc(x_21);
x_24 = l_ByteArray_extract(x_20, x_21, x_23);
lean_dec(x_23);
x_25 = lean_byte_array_size(x_24);
x_26 = lean_nat_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_st_ref_set(x_1, x_27, x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_byte_array_size(x_2);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_14 = lean_byte_array_copy_slice(x_2, x_10, x_8, x_9, x_11, x_13);
x_15 = lean_nat_add(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_14);
x_16 = lean_st_ref_set(x_1, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_byte_array_size(x_2);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
lean_inc(x_24);
lean_inc(x_22);
x_27 = lean_byte_array_copy_slice(x_2, x_23, x_21, x_22, x_24, x_26);
x_28 = lean_nat_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_string_to_utf8(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_byte_array_size(x_10);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_12);
lean_inc(x_9);
x_15 = lean_byte_array_copy_slice(x_10, x_11, x_8, x_9, x_12, x_14);
lean_dec(x_10);
x_16 = lean_nat_add(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_5, 0, x_15);
x_17 = lean_st_ref_set(x_1, x_5, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_string_to_utf8(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_byte_array_size(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_26);
lean_inc(x_23);
x_29 = lean_byte_array_copy_slice(x_24, x_25, x_22, x_23, x_26, x_28);
lean_dec(x_24);
x_30 = lean_nat_add(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_st_ref_set(x_1, x_31, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
static lean_object* _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8", 13, 13);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_ofBuffer___lam__3___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_26; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_8 = x_4;
} else {
 lean_dec_ref(x_4);
 x_8 = lean_box(0);
}
lean_inc(x_7);
x_26 = l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0(x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_byte_array_size(x_6);
x_9 = x_27;
goto block_25;
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_byte_array_get(x_6, x_28);
x_30 = 0;
x_31 = lean_uint8_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_28, x_32);
lean_dec(x_28);
x_9 = x_33;
goto block_25;
}
else
{
x_9 = x_28;
goto block_25;
}
}
block_25:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_9);
lean_inc(x_6);
if (lean_is_scalar(x_8)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_8;
}
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_st_ref_set(x_1, x_10, x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = l_ByteArray_extract(x_6, x_7, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_15 = lean_string_validate_utf8(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
x_16 = l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; 
x_17 = lean_string_from_utf8_unchecked(x_14);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_ByteArray_extract(x_6, x_7, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_20 = lean_string_validate_utf8(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
x_21 = l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_string_from_utf8_unchecked(x_19);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__5(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__4), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__5___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_4);
lean_ctor_set(x_10, 5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_findIdx_x3f_loop___at___IO_FS_Stream_ofBuffer_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofBuffer___lam__0(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___lam__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_Stream_ofBuffer___lam__5(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_ref_get(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_string_validate_utf8(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
x_11 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4;
x_12 = l_panic___redArg(x_10, x_11);
x_4 = x_12;
goto block_7;
}
else
{
lean_object* x_13; 
x_13 = lean_string_from_utf8_unchecked(x_8);
x_4 = x_13;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_3);
x_12 = l_IO_FS_Stream_ofBuffer(x_4);
x_13 = l_IO_FS_Stream_ofBuffer(x_9);
if (x_7 == 0)
{
x_14 = x_8;
goto block_18;
}
else
{
lean_object* x_19; 
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_IO_withStderr___redArg(x_5, x_6, x_2, x_13, x_8);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_IO_withStdout___redArg(x_5, x_6, x_2, x_13, x_14);
x_16 = l_IO_withStdin___redArg(x_5, x_6, x_2, x_12, x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_6);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_10);
lean_closure_set(x_11, 7, x_7);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_IO_FS_Handle_readBinToEnd___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_withIsolatedStreams___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_IO_mkRef), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_withIsolatedStreams___redArg___closed__1;
lean_inc(x_3);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_box(x_5);
lean_inc(x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_2);
lean_closure_set(x_12, 5, x_11);
lean_closure_set(x_12, 6, x_4);
lean_closure_set(x_12, 7, x_10);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_withIsolatedStreams___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_withIsolatedStreams___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_IO_FS_withIsolatedStreams___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_IO_FS_withIsolatedStreams___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_IO_FS_withIsolatedStreams___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_IO_FS_withIsolatedStreams(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termPrintln!__", 14, 14);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("println! ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_termPrintln_x21_______closed__11;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_______closed__12;
x_2 = l_termPrintln_x21_______closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__12;
x_2 = l_termPrintln_x21_______closed__13;
x_3 = l_termPrintln_x21_______closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__14;
x_2 = l_termPrintln_x21_______closed__5;
x_3 = l_termPrintln_x21_______closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__15;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_termPrintln_x21_______closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21____() {
_start:
{
lean_object* x_1; 
x_1 = l_termPrintln_x21_______closed__16;
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
x_2 = l___auto___closed__14____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.println", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO", 2, 2);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("println", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
x_2 = l___auto___closed__14____x40_Init_System_IO___hyg_1906_;
x_3 = l___auto___closed__1____x40_Init_System_IO___hyg_1906_;
x_4 = l___auto___closed__0____x40_Init_System_IO___hyg_1906_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termS!_", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("s!", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_termPrintln_x21_______closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_SourceInfo_fromRef(x_14, x_11);
lean_dec(x_14);
x_16 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_17 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___auto___closed__16____x40_Init_System_IO___hyg_1906_;
x_20 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_21 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_addMacroScope(x_12, x_21, x_13);
x_23 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
lean_inc(x_15);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = l___auto___closed__9____x40_Init_System_IO___hyg_1906_;
lean_inc(x_15);
x_26 = l_Lean_Syntax_node1(x_15, x_25, x_9);
lean_inc(x_15);
x_27 = l_Lean_Syntax_node2(x_15, x_19, x_24, x_26);
x_28 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_31 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
lean_inc(x_13);
lean_inc(x_12);
x_32 = l_Lean_addMacroScope(x_12, x_31, x_13);
x_33 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_15);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_36 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_37 = l_Lean_addMacroScope(x_12, x_36, x_13);
x_38 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
lean_inc(x_15);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_inc(x_15);
x_40 = l_Lean_Syntax_node1(x_15, x_25, x_39);
lean_inc(x_15);
x_41 = l_Lean_Syntax_node2(x_15, x_19, x_34, x_40);
lean_inc(x_15);
x_42 = l_Lean_Syntax_node1(x_15, x_25, x_41);
x_43 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_inc(x_15);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Syntax_node5(x_15, x_16, x_18, x_27, x_29, x_42, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_SourceInfo_fromRef(x_49, x_51);
lean_dec(x_49);
x_53 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_54 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___auto___closed__16____x40_Init_System_IO___hyg_1906_;
x_57 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_58 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_48);
lean_inc(x_47);
x_59 = l_Lean_addMacroScope(x_47, x_58, x_48);
x_60 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
lean_inc(x_52);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = l___auto___closed__9____x40_Init_System_IO___hyg_1906_;
x_63 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
x_64 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
x_65 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_52);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_52);
x_67 = l_Lean_Syntax_node2(x_52, x_64, x_66, x_9);
x_68 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_inc(x_52);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_69);
lean_inc(x_55);
lean_inc(x_52);
x_70 = l_Lean_Syntax_node3(x_52, x_63, x_55, x_67, x_69);
lean_inc(x_52);
x_71 = l_Lean_Syntax_node1(x_52, x_62, x_70);
lean_inc(x_52);
x_72 = l_Lean_Syntax_node2(x_52, x_56, x_61, x_71);
x_73 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_inc(x_52);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_52);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_76 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
lean_inc(x_48);
lean_inc(x_47);
x_77 = l_Lean_addMacroScope(x_47, x_76, x_48);
x_78 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_52);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_52);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_78);
x_80 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_81 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_82 = l_Lean_addMacroScope(x_47, x_81, x_48);
x_83 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
lean_inc(x_52);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_52);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_83);
lean_inc(x_52);
x_85 = l_Lean_Syntax_node1(x_52, x_62, x_84);
lean_inc(x_52);
x_86 = l_Lean_Syntax_node2(x_52, x_56, x_79, x_85);
lean_inc(x_52);
x_87 = l_Lean_Syntax_node1(x_52, x_62, x_86);
x_88 = l_Lean_Syntax_node5(x_52, x_53, x_55, x_72, x_74, x_87, x_69);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_mark_multi_threaded(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_mark_persistent(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_forget(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_System_IOError(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_ST(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IOError(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instMonadEIO___closed__0 = _init_l_instMonadEIO___closed__0();
lean_mark_persistent(l_instMonadEIO___closed__0);
l_instMonadEIO___closed__1 = _init_l_instMonadEIO___closed__1();
lean_mark_persistent(l_instMonadEIO___closed__1);
l_instMonadEIO___closed__2 = _init_l_instMonadEIO___closed__2();
lean_mark_persistent(l_instMonadEIO___closed__2);
l_instMonadEIO___closed__3 = _init_l_instMonadEIO___closed__3();
lean_mark_persistent(l_instMonadEIO___closed__3);
l_instMonadEIO___closed__4 = _init_l_instMonadEIO___closed__4();
lean_mark_persistent(l_instMonadEIO___closed__4);
l_instMonadEIO___closed__5 = _init_l_instMonadEIO___closed__5();
lean_mark_persistent(l_instMonadEIO___closed__5);
l_instMonadEIO___closed__6 = _init_l_instMonadEIO___closed__6();
lean_mark_persistent(l_instMonadEIO___closed__6);
l_instMonadEIO___closed__7 = _init_l_instMonadEIO___closed__7();
lean_mark_persistent(l_instMonadEIO___closed__7);
l_instMonadEIO___closed__8 = _init_l_instMonadEIO___closed__8();
lean_mark_persistent(l_instMonadEIO___closed__8);
l_instMonadEIO___closed__9 = _init_l_instMonadEIO___closed__9();
lean_mark_persistent(l_instMonadEIO___closed__9);
l_instMonadFinallyEIO___closed__0 = _init_l_instMonadFinallyEIO___closed__0();
lean_mark_persistent(l_instMonadFinallyEIO___closed__0);
l_instMonadExceptOfEIO___closed__0 = _init_l_instMonadExceptOfEIO___closed__0();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__0);
l_instMonadExceptOfEIO___closed__1 = _init_l_instMonadExceptOfEIO___closed__1();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__1);
l_instOrElseEIO___closed__0 = _init_l_instOrElseEIO___closed__0();
lean_mark_persistent(l_instOrElseEIO___closed__0);
l_instOrElseEIO___closed__1 = _init_l_instOrElseEIO___closed__1();
lean_mark_persistent(l_instOrElseEIO___closed__1);
l_instOrElseEIO___closed__2 = _init_l_instOrElseEIO___closed__2();
lean_mark_persistent(l_instOrElseEIO___closed__2);
l_instMonadBaseIO___closed__0 = _init_l_instMonadBaseIO___closed__0();
lean_mark_persistent(l_instMonadBaseIO___closed__0);
l_instMonadBaseIO = _init_l_instMonadBaseIO();
lean_mark_persistent(l_instMonadBaseIO);
l_instMonadFinallyBaseIO = _init_l_instMonadFinallyBaseIO();
lean_mark_persistent(l_instMonadFinallyBaseIO);
l_IO_instInhabitedTaskState = _init_l_IO_instInhabitedTaskState();
l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__0____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__1____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__2____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__3____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__4____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__5____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__6____x40_Init_System_IO___hyg_1435_);
l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_ = _init_l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_();
lean_mark_persistent(l_IO_reprTaskState___closed__7____x40_Init_System_IO___hyg_1435_);
l_IO_instReprTaskState___closed__0 = _init_l_IO_instReprTaskState___closed__0();
lean_mark_persistent(l_IO_instReprTaskState___closed__0);
l_IO_instReprTaskState = _init_l_IO_instReprTaskState();
lean_mark_persistent(l_IO_instReprTaskState);
l_IO_instOrdTaskState___closed__0 = _init_l_IO_instOrdTaskState___closed__0();
lean_mark_persistent(l_IO_instOrdTaskState___closed__0);
l_IO_instOrdTaskState = _init_l_IO_instOrdTaskState();
lean_mark_persistent(l_IO_instOrdTaskState);
l_IO_instLTTaskState = _init_l_IO_instLTTaskState();
lean_mark_persistent(l_IO_instLTTaskState);
l_IO_instLETaskState = _init_l_IO_instLETaskState();
lean_mark_persistent(l_IO_instLETaskState);
l_IO_instMinTaskState = _init_l_IO_instMinTaskState();
lean_mark_persistent(l_IO_instMinTaskState);
l_IO_instMaxTaskState = _init_l_IO_instMaxTaskState();
lean_mark_persistent(l_IO_instMaxTaskState);
l_IO_TaskState_toString___closed__0 = _init_l_IO_TaskState_toString___closed__0();
lean_mark_persistent(l_IO_TaskState_toString___closed__0);
l_IO_TaskState_toString___closed__1 = _init_l_IO_TaskState_toString___closed__1();
lean_mark_persistent(l_IO_TaskState_toString___closed__1);
l_IO_TaskState_toString___closed__2 = _init_l_IO_TaskState_toString___closed__2();
lean_mark_persistent(l_IO_TaskState_toString___closed__2);
l_IO_instToStringTaskState___closed__0 = _init_l_IO_instToStringTaskState___closed__0();
lean_mark_persistent(l_IO_instToStringTaskState___closed__0);
l_IO_instToStringTaskState = _init_l_IO_instToStringTaskState();
lean_mark_persistent(l_IO_instToStringTaskState);
l___auto___closed__0____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__0____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__0____x40_Init_System_IO___hyg_1906_);
l___auto___closed__1____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__1____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__1____x40_Init_System_IO___hyg_1906_);
l___auto___closed__2____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__2____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__2____x40_Init_System_IO___hyg_1906_);
l___auto___closed__3____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__3____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__3____x40_Init_System_IO___hyg_1906_);
l___auto___closed__4____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__4____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__4____x40_Init_System_IO___hyg_1906_);
l___auto___closed__5____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__5____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__5____x40_Init_System_IO___hyg_1906_);
l___auto___closed__6____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__6____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__6____x40_Init_System_IO___hyg_1906_);
l___auto___closed__7____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__7____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__7____x40_Init_System_IO___hyg_1906_);
l___auto___closed__8____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__8____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__8____x40_Init_System_IO___hyg_1906_);
l___auto___closed__9____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__9____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__9____x40_Init_System_IO___hyg_1906_);
l___auto___closed__10____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__10____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__10____x40_Init_System_IO___hyg_1906_);
l___auto___closed__11____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__11____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__11____x40_Init_System_IO___hyg_1906_);
l___auto___closed__12____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__12____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__12____x40_Init_System_IO___hyg_1906_);
l___auto___closed__13____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__13____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__13____x40_Init_System_IO___hyg_1906_);
l___auto___closed__14____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__14____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__14____x40_Init_System_IO___hyg_1906_);
l___auto___closed__15____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__15____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__15____x40_Init_System_IO___hyg_1906_);
l___auto___closed__16____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__16____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__16____x40_Init_System_IO___hyg_1906_);
l___auto___closed__17____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__17____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__17____x40_Init_System_IO___hyg_1906_);
l___auto___closed__18____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__18____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__18____x40_Init_System_IO___hyg_1906_);
l___auto___closed__19____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__19____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__19____x40_Init_System_IO___hyg_1906_);
l___auto___closed__20____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__20____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__20____x40_Init_System_IO___hyg_1906_);
l___auto___closed__21____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__21____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__21____x40_Init_System_IO___hyg_1906_);
l___auto___closed__22____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__22____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__22____x40_Init_System_IO___hyg_1906_);
l___auto___closed__23____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__23____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__23____x40_Init_System_IO___hyg_1906_);
l___auto___closed__24____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__24____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__24____x40_Init_System_IO___hyg_1906_);
l___auto___closed__25____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__25____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__25____x40_Init_System_IO___hyg_1906_);
l___auto___closed__26____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__26____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__26____x40_Init_System_IO___hyg_1906_);
l___auto___closed__27____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__27____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__27____x40_Init_System_IO___hyg_1906_);
l___auto___closed__28____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__28____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__28____x40_Init_System_IO___hyg_1906_);
l___auto___closed__29____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__29____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__29____x40_Init_System_IO___hyg_1906_);
l___auto___closed__30____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__30____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__30____x40_Init_System_IO___hyg_1906_);
l___auto___closed__31____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__31____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__31____x40_Init_System_IO___hyg_1906_);
l___auto___closed__32____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__32____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__32____x40_Init_System_IO___hyg_1906_);
l___auto___closed__33____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__33____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__33____x40_Init_System_IO___hyg_1906_);
l___auto___closed__34____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__34____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__34____x40_Init_System_IO___hyg_1906_);
l___auto___closed__35____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__35____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__35____x40_Init_System_IO___hyg_1906_);
l___auto___closed__36____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__36____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__36____x40_Init_System_IO___hyg_1906_);
l___auto___closed__37____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__37____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__37____x40_Init_System_IO___hyg_1906_);
l___auto___closed__38____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__38____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__38____x40_Init_System_IO___hyg_1906_);
l___auto___closed__39____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__39____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__39____x40_Init_System_IO___hyg_1906_);
l___auto___closed__40____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__40____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__40____x40_Init_System_IO___hyg_1906_);
l___auto___closed__41____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__41____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__41____x40_Init_System_IO___hyg_1906_);
l___auto___closed__42____x40_Init_System_IO___hyg_1906_ = _init_l___auto___closed__42____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto___closed__42____x40_Init_System_IO___hyg_1906_);
l___auto____x40_Init_System_IO___hyg_1906_ = _init_l___auto____x40_Init_System_IO___hyg_1906_();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1906_);
l_IO_FS_Mode_noConfusion___redArg___closed__0 = _init_l_IO_FS_Mode_noConfusion___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Mode_noConfusion___redArg___closed__0);
l_IO_FS_instInhabitedStream___lam__0___closed__0 = _init_l_IO_FS_instInhabitedStream___lam__0___closed__0();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lam__0___closed__0);
l_IO_FS_instInhabitedStream___lam__0___closed__1 = _init_l_IO_FS_instInhabitedStream___lam__0___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lam__0___closed__1);
l_IO_FS_instInhabitedStream___closed__0 = _init_l_IO_FS_instInhabitedStream___closed__0();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__0);
l_IO_FS_instInhabitedStream = _init_l_IO_FS_instInhabitedStream();
lean_mark_persistent(l_IO_FS_instInhabitedStream);
l_IO_FS_Handle_readBinToEnd___closed__0 = _init_l_IO_FS_Handle_readBinToEnd___closed__0();
lean_mark_persistent(l_IO_FS_Handle_readBinToEnd___closed__0);
l_IO_FS_Handle_readToEnd___closed__0 = _init_l_IO_FS_Handle_readToEnd___closed__0();
lean_mark_persistent(l_IO_FS_Handle_readToEnd___closed__0);
l_IO_FS_Handle_readToEnd___closed__1 = _init_l_IO_FS_Handle_readToEnd___closed__1();
lean_mark_persistent(l_IO_FS_Handle_readToEnd___closed__1);
l_IO_FS_lines___closed__0 = _init_l_IO_FS_lines___closed__0();
lean_mark_persistent(l_IO_FS_lines___closed__0);
l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__0____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__1____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__2____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__3____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__4____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__5____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__6____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__7____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__8____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__9____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__10____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__11____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__12____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__13____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__14____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__15____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__16____x40_Init_System_IO___hyg_2816_);
l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_ = _init_l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_();
lean_mark_persistent(l_IO_FS_reprDirEntry___redArg___closed__17____x40_Init_System_IO___hyg_2816_);
l_IO_FS_instReprDirEntry___closed__0 = _init_l_IO_FS_instReprDirEntry___closed__0();
lean_mark_persistent(l_IO_FS_instReprDirEntry___closed__0);
l_IO_FS_instReprDirEntry = _init_l_IO_FS_instReprDirEntry();
lean_mark_persistent(l_IO_FS_instReprDirEntry);
l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__0____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__1____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__2____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__3____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__4____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__5____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__6____x40_Init_System_IO___hyg_2894_);
l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_ = _init_l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_();
lean_mark_persistent(l_IO_FS_reprFileType___closed__7____x40_Init_System_IO___hyg_2894_);
l_IO_FS_instReprFileType___closed__0 = _init_l_IO_FS_instReprFileType___closed__0();
lean_mark_persistent(l_IO_FS_instReprFileType___closed__0);
l_IO_FS_instReprFileType = _init_l_IO_FS_instReprFileType();
lean_mark_persistent(l_IO_FS_instReprFileType);
l_IO_FS_instBEqFileType___closed__0 = _init_l_IO_FS_instBEqFileType___closed__0();
lean_mark_persistent(l_IO_FS_instBEqFileType___closed__0);
l_IO_FS_instBEqFileType = _init_l_IO_FS_instBEqFileType();
lean_mark_persistent(l_IO_FS_instBEqFileType);
l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__0____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__1____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__2____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__3____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__4____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__5____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__6____x40_Init_System_IO___hyg_3085_);
l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_ = _init_l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_();
lean_mark_persistent(l_IO_FS_reprSystemTime___redArg___closed__7____x40_Init_System_IO___hyg_3085_);
l_IO_FS_instReprSystemTime___closed__0 = _init_l_IO_FS_instReprSystemTime___closed__0();
lean_mark_persistent(l_IO_FS_instReprSystemTime___closed__0);
l_IO_FS_instReprSystemTime = _init_l_IO_FS_instReprSystemTime();
lean_mark_persistent(l_IO_FS_instReprSystemTime);
l_IO_FS_instBEqSystemTime___closed__0 = _init_l_IO_FS_instBEqSystemTime___closed__0();
lean_mark_persistent(l_IO_FS_instBEqSystemTime___closed__0);
l_IO_FS_instBEqSystemTime = _init_l_IO_FS_instBEqSystemTime();
lean_mark_persistent(l_IO_FS_instBEqSystemTime);
l_IO_FS_instOrdSystemTime___closed__0 = _init_l_IO_FS_instOrdSystemTime___closed__0();
lean_mark_persistent(l_IO_FS_instOrdSystemTime___closed__0);
l_IO_FS_instOrdSystemTime = _init_l_IO_FS_instOrdSystemTime();
lean_mark_persistent(l_IO_FS_instOrdSystemTime);
l_IO_FS_instInhabitedSystemTime___closed__0 = _init_l_IO_FS_instInhabitedSystemTime___closed__0();
l_IO_FS_instInhabitedSystemTime___closed__1 = _init_l_IO_FS_instInhabitedSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime___closed__1);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__0____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__1____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__2____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__3____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__4____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__5____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__6____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__7____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__8____x40_Init_System_IO___hyg_3346_);
l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_ = _init_l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_();
lean_mark_persistent(l_IO_FS_reprMetadata___redArg___closed__9____x40_Init_System_IO___hyg_3346_);
l_IO_FS_instReprMetadata___closed__0 = _init_l_IO_FS_instReprMetadata___closed__0();
lean_mark_persistent(l_IO_FS_instReprMetadata___closed__0);
l_IO_FS_instReprMetadata = _init_l_IO_FS_instReprMetadata();
lean_mark_persistent(l_IO_FS_instReprMetadata);
l_IO_FS_readBinFile___closed__0 = _init_l_IO_FS_readBinFile___closed__0();
lean_mark_persistent(l_IO_FS_readBinFile___closed__0);
l_IO_FS_readFile___closed__0 = _init_l_IO_FS_readFile___closed__0();
lean_mark_persistent(l_IO_FS_readFile___closed__0);
l_IO_FS_readFile___closed__1 = _init_l_IO_FS_readFile___closed__1();
lean_mark_persistent(l_IO_FS_readFile___closed__1);
l_IO_withStdout___redArg___closed__0 = _init_l_IO_withStdout___redArg___closed__0();
lean_mark_persistent(l_IO_withStdout___redArg___closed__0);
l_IO_println___redArg___closed__0 = _init_l_IO_println___redArg___closed__0();
lean_mark_persistent(l_IO_println___redArg___closed__0);
l_IO_appDir___closed__0 = _init_l_IO_appDir___closed__0();
lean_mark_persistent(l_IO_appDir___closed__0);
l_IO_appDir___closed__1 = _init_l_IO_appDir___closed__1();
lean_mark_persistent(l_IO_appDir___closed__1);
l_IO_FS_withTempFile___redArg___closed__0 = _init_l_IO_FS_withTempFile___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withTempFile___redArg___closed__0);
l_IO_FS_withTempDir___redArg___closed__0 = _init_l_IO_FS_withTempDir___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withTempDir___redArg___closed__0);
l_IO_Process_output___closed__0 = _init_l_IO_Process_output___closed__0();
lean_mark_persistent(l_IO_Process_output___closed__0);
l_IO_Process_run___closed__0 = _init_l_IO_Process_run___closed__0();
lean_mark_persistent(l_IO_Process_run___closed__0);
l_IO_Process_run___closed__1 = _init_l_IO_Process_run___closed__1();
lean_mark_persistent(l_IO_Process_run___closed__1);
l_IO_Process_run___closed__2 = _init_l_IO_Process_run___closed__2();
lean_mark_persistent(l_IO_Process_run___closed__2);
l_IO_instMonadLiftSTRealWorldBaseIO = _init_l_IO_instMonadLiftSTRealWorldBaseIO();
lean_mark_persistent(l_IO_instMonadLiftSTRealWorldBaseIO);
l_IO_FS_Stream_ofBuffer___lam__3___closed__0 = _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__0();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___lam__3___closed__0);
l_IO_FS_Stream_ofBuffer___lam__3___closed__1 = _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__1();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___lam__3___closed__1);
l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0 = _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0);
l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1 = _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1);
l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2 = _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2);
l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3 = _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3);
l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4 = _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
l_IO_FS_withIsolatedStreams___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___closed__0);
l_IO_FS_withIsolatedStreams___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___redArg___closed__1);
l_termPrintln_x21_______closed__0 = _init_l_termPrintln_x21_______closed__0();
lean_mark_persistent(l_termPrintln_x21_______closed__0);
l_termPrintln_x21_______closed__1 = _init_l_termPrintln_x21_______closed__1();
lean_mark_persistent(l_termPrintln_x21_______closed__1);
l_termPrintln_x21_______closed__2 = _init_l_termPrintln_x21_______closed__2();
lean_mark_persistent(l_termPrintln_x21_______closed__2);
l_termPrintln_x21_______closed__3 = _init_l_termPrintln_x21_______closed__3();
lean_mark_persistent(l_termPrintln_x21_______closed__3);
l_termPrintln_x21_______closed__4 = _init_l_termPrintln_x21_______closed__4();
lean_mark_persistent(l_termPrintln_x21_______closed__4);
l_termPrintln_x21_______closed__5 = _init_l_termPrintln_x21_______closed__5();
lean_mark_persistent(l_termPrintln_x21_______closed__5);
l_termPrintln_x21_______closed__6 = _init_l_termPrintln_x21_______closed__6();
lean_mark_persistent(l_termPrintln_x21_______closed__6);
l_termPrintln_x21_______closed__7 = _init_l_termPrintln_x21_______closed__7();
lean_mark_persistent(l_termPrintln_x21_______closed__7);
l_termPrintln_x21_______closed__8 = _init_l_termPrintln_x21_______closed__8();
lean_mark_persistent(l_termPrintln_x21_______closed__8);
l_termPrintln_x21_______closed__9 = _init_l_termPrintln_x21_______closed__9();
lean_mark_persistent(l_termPrintln_x21_______closed__9);
l_termPrintln_x21_______closed__10 = _init_l_termPrintln_x21_______closed__10();
lean_mark_persistent(l_termPrintln_x21_______closed__10);
l_termPrintln_x21_______closed__11 = _init_l_termPrintln_x21_______closed__11();
lean_mark_persistent(l_termPrintln_x21_______closed__11);
l_termPrintln_x21_______closed__12 = _init_l_termPrintln_x21_______closed__12();
lean_mark_persistent(l_termPrintln_x21_______closed__12);
l_termPrintln_x21_______closed__13 = _init_l_termPrintln_x21_______closed__13();
lean_mark_persistent(l_termPrintln_x21_______closed__13);
l_termPrintln_x21_______closed__14 = _init_l_termPrintln_x21_______closed__14();
lean_mark_persistent(l_termPrintln_x21_______closed__14);
l_termPrintln_x21_______closed__15 = _init_l_termPrintln_x21_______closed__15();
lean_mark_persistent(l_termPrintln_x21_______closed__15);
l_termPrintln_x21_______closed__16 = _init_l_termPrintln_x21_______closed__16();
lean_mark_persistent(l_termPrintln_x21_______closed__16);
l_termPrintln_x21____ = _init_l_termPrintln_x21____();
lean_mark_persistent(l_termPrintln_x21____);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
