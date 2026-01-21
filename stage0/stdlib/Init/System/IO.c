// Lean compiler output
// Module: Init.System.IO
// Imports: public import Init.System.IOError public import Init.System.FilePath public import Init.Data.Ord.UInt import Init.Data.String.TakeDrop import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprFileType_repr___closed__7;
static uint32_t l_IO_FS_instInhabitedSystemTime_default___closed__0;
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__0;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__38;
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_termPrintln_x21_____00__closed__9;
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object*, lean_object*);
static lean_object* l_instOrElseEIO___closed__0;
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_termPrintln_x21____;
static lean_object* l_IO_waitAny___auto__1___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__0;
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__39;
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
LEAN_EXPORT lean_object* l_IO_println(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__0;
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_io_check_canceled();
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object*, lean_object*);
uint64_t lean_io_get_tid();
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__4;
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__10;
lean_object* lean_io_create_tempdir();
LEAN_EXPORT lean_object* l_EIO_throw(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__8;
static lean_object* l_IO_FS_instReprFileType___closed__0;
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprFileType_repr___closed__0;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(size_t);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_println___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__6;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__15;
lean_object* lean_io_prim_handle_flush(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33;
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__0;
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__1;
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t, uint8_t);
static lean_object* l_termPrintln_x21_____00__closed__1;
lean_object* lean_io_rename(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO;
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__33;
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1;
lean_object* lean_io_getenv(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprFileType_repr___closed__5;
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__18;
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_termPrintln_x21_____00__closed__13;
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__4;
static lean_object* l_IO_FS_instReprSystemTime___closed__0;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__3;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime;
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t);
static lean_object* l_IO_FS_instInhabitedStream_default___closed__0;
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO;
static lean_object* l_IO_Process_run___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__0;
static lean_object* l_IO_FS_readBinFile___closed__0;
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object*, lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__2;
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_force_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__7;
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t, uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_IO_FS_instInhabitedStream_default___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream;
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_get_stdout();
static lean_object* l_termPrintln_x21_____00__closed__4;
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState_default;
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instReprTaskState;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0();
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__4;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
static lean_object* l_instMonadAttachBaseIO___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Process_output___closed__1;
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_new();
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream_default___closed__1;
static lean_object* l_IO_waitAny___auto__1___closed__31;
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState;
lean_object* l_instMonadAttachEST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_instToStringTaskState___closed__0;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadFinallyST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_IO_withStdin___redArg___closed__0;
static lean_object* l_IO_FS_Stream_readToEnd___closed__0;
lean_object* lean_io_set_heartbeats(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readToEnd___closed__1;
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
static lean_object* l_IO_FS_instReprFileType_repr___closed__6;
lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_io_timeit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_IO_waitAny___auto__1___closed__20;
LEAN_EXPORT lean_object* l_IO_waitAny_x27___auto__1;
lean_object* l_instMonadEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Process_output___closed__0;
LEAN_EXPORT lean_object* l_IO_instLTTaskState;
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime_default;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__1;
static lean_object* l_IO_waitAny___auto__1___closed__28;
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_IO_FS_Handle_lines___closed__0;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40;
static lean_object* l_IO_waitAny_x27___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_RealWorld_nonemptyType;
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMinTaskState;
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object*);
lean_object* lean_io_wait_any(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__37;
static lean_object* l_instMonadFinallyEIO___closed__0;
static lean_object* l_IO_FS_withTempDir___redArg___closed__0;
static lean_object* l_IO_waitAny___auto__1___closed__9;
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__5;
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_IO_instMinTaskState___closed__0;
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__12;
static lean_object* l_IO_waitAny___auto__1___closed__6;
static lean_object* l_IO_FS_instInhabitedStream_default___closed__6;
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t);
static lean_object* l_IO_waitAny___auto__1___closed__22;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__32;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__0;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_IO_appDir();
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__12;
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object*);
static lean_object* l_instMonadFinallyBaseIO___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0;
lean_object* lean_get_stdin();
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__9;
static lean_object* l_IO_waitAny___auto__1___closed__21;
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_prim_handle_is_tty(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_get_stderr();
static lean_object* l_IO_instReprTaskState___closed__0;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3();
static lean_object* l_IO_waitAny___auto__1___closed__40;
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_multi_threaded(lean_object*);
static lean_object* l_IO_FS_readFile___closed__0;
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__2;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__15;
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadAttachEIO___closed__0;
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_create_tempfile();
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__23;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__35;
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object*);
static lean_object* l_IO_FS_instInhabitedStream_default___closed__4;
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__13;
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry___closed__0;
static lean_object* l_IO_waitAny___auto__1___closed__19;
lean_object* lean_task_get_own(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object*);
static lean_object* l_IO_FS_readFile___closed__1;
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprFileType_repr___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object*);
lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry;
LEAN_EXPORT lean_object* l_IO_instToStringTaskState;
lean_object* lean_io_process_set_current_dir(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__17;
static lean_object* l_IO_FS_instReprMetadata___closed__0;
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withTempFile___redArg___closed__0;
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t);
static lean_object* l_IO_FS_instReprFileType_repr___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__12;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object*);
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__8;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__15;
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__2;
static lean_object* l_termPrintln_x21_____00__closed__5;
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t, uint8_t);
static lean_object* l_IO_waitAny___auto__1___closed__11;
static lean_object* l_IO_instReprTaskState_repr___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__16;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream_default___closed__5;
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__1;
static lean_object* l_IO_Process_run___closed__2;
uint32_t lean_io_process_child_pid(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__16;
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__16;
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__24;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__3;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__8;
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType;
lean_object* lean_io_app_path();
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__5;
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_object* lean_io_realpath(lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__29;
static lean_object* l_termPrintln_x21_____00__closed__10;
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__2;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_chmod(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType;
LEAN_EXPORT lean_object* l_IO_instMaxTaskState;
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object*);
lean_object* l_instMonadAttachST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_IO_instReprTaskState_repr___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO;
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__14;
LEAN_EXPORT lean_object* l_IO_instOrdTaskState;
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instOrElseEIO___closed__1;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2;
static lean_object* l_IO_waitAny___auto__1___closed__42;
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object*, lean_object*);
static lean_object* l_IO_TaskState_toString___closed__2;
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
uint8_t lean_io_initializing();
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_instLETaskState;
static lean_object* l_IO_waitAny___auto__1___closed__0;
static lean_object* l_IO_FS_instReprFileType_repr___closed__4;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__8;
lean_object* lean_io_read_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Handle_readToEnd___closed__1;
static lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default;
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_current_dir();
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
static lean_object* l_IO_FS_instBEqFileType___closed__0;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprFileType_repr___closed__2;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__2;
static lean_object* l_IO_instMaxTaskState___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__14;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
static lean_object* l_IO_TaskState_toString___closed__0;
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instOrdSystemTime___closed__0;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__11;
static lean_object* l_IO_instOrdTaskState___closed__0;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
lean_object* lean_io_prim_handle_truncate(lean_object*);
static lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__6;
static lean_object* l_IO_FS_instInhabitedStream_default___closed__2;
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__0;
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__41;
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__30;
static lean_object* l_IO_FS_instInhabitedSystemTime_default___closed__1;
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
static lean_object* l_IO_FS_instBEqSystemTime___closed__0;
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
uint32_t lean_io_process_get_pid();
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*);
static lean_object* l_IO_instReprTaskState_repr___closed__1;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__6;
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object*);
static lean_object* l_instMonadLiftBaseIOEIO___closed__0;
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object*);
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__2;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__25;
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
static lean_object* l_IO_waitAny___auto__1___closed__27;
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_object* lean_io_process_child_kill(lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__0;
LEAN_EXPORT lean_object* l_IO_waitAny___auto__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Handle_readToEnd___closed__0;
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_____00__closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__34;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object*);
static lean_object* l_instMonadBaseIO___closed__0;
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t, uint8_t);
static lean_object* l_IO_TaskState_toString___closed__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_waitAny___auto__1___closed__36;
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t, uint8_t);
lean_object* lean_io_create_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_get_current_dir();
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_IO_RealWorld_nonemptyType() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_instMonadBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
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
static lean_object* _init_l_instMonadFinallyBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadFinallyST___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadFinallyBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadFinallyBaseIO___closed__0;
return x_1;
}
}
static lean_object* _init_l_instMonadAttachBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadAttachST___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_instMonadAttachBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadAttachBaseIO___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, lean_box(0));
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BaseIO_map___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_4, lean_box(0));
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_BaseIO_map(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, lean_box(0));
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BaseIO_toEIO___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_3, lean_box(0));
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BaseIO_toEIO(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instMonadLiftBaseIOEIO___lam__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_instMonadLiftBaseIOEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadLiftBaseIOEIO___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_toBaseIO___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_ctor_set_tag(x_5, 0);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_toBaseIO(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_catchExceptions___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_apply_2(x_4, x_8, lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_catchExceptions(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_instMonadEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadEIO___closed__0;
return x_2;
}
}
static lean_object* _init_l_instMonadFinallyEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadFinallyEST___lam__0___boxed), 5, 0);
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
static lean_object* _init_l_instMonadAttachEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadAttachEST___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadAttachEIO___closed__0;
return x_2;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadExceptOfEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadExceptOfEIO___closed__0;
return x_2;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadExceptOfEIO___closed__0;
x_2 = l_instMonadExceptOfMonadExceptOf___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_instOrElseEIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instOrElseEIO___closed__0;
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
x_3 = l_instOrElseEIO___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_apply_1(x_1, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_map___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_apply_1(x_4, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_1(x_4, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_EIO_map(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_throw___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_throw(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_throw(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_tryCatch___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_tryCatch(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_ofExcept___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_ofExcept(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_adapt___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_apply_1(x_4, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_apply_1(x_4, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_EIO_adapt(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_adaptExcept___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_apply_1(x_4, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_apply_1(x_4, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_EIO_adaptExcept(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, lean_box(0));
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BaseIO_toIO___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BaseIO_toIO(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_toIO___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_apply_1(x_3, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_apply_1(x_3, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_toIO(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
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
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_toIO_x27___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, lean_box(0));
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EIO_toIO_x27(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_toEIO___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, lean_box(0));
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_apply_1(x_3, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_apply_1(x_3, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_toEIO(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
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
x_2 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
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
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
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
x_2 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
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
x_3 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
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
x_5 = lean_io_timeit(x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_allocprof(x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_io_initializing();
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_as_task(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = lean_io_map_task(x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = lean_io_bind_task(x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_io_map_task(x_2, x_1, x_3, x_4);
lean_dec_ref(x_6);
x_7 = lean_box(0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_BaseIO_chainTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_BaseIO_chainTask___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l_BaseIO_chainTask(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = l_List_reverse___redArg(x_5);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (x_3 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_List_reverse___redArg(x_5);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_io_as_task(x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = l_List_reverse___redArg(x_5);
x_11 = lean_apply_2(x_1, x_10, lean_box(0));
x_12 = lean_task_pure(x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
x_16 = lean_io_map_task(x_15, x_14, x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_13);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec_ref(x_4);
x_18 = lean_box(x_3);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_13);
x_20 = lean_io_bind_task(x_17, x_19, x_2, x_3);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_9 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l___private_Init_System_IO_0__BaseIO_mapTasks_go(x_1, x_2, x_3, x_4, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(x_1, x_3, x_4, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_BaseIO_mapTasks___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_BaseIO_mapTasks___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_BaseIO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
x_5 = lean_io_as_task(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_asTask___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
x_7 = lean_io_as_task(x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_asTask(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_mapTask___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_io_map_task(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_EIO_mapTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_io_map_task(x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l_EIO_mapTask(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_4, 0);
x_7 = lean_task_pure(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_bindTask___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_bind_task(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_EIO_bindTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = lean_io_bind_task(x_4, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l_EIO_bindTask(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_chainTask___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_map_task(x_6, x_1, x_3, x_4);
lean_dec_ref(x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_EIO_chainTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_EIO_chainTask___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_EIO_chainTask(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_EIO_mapTasks___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_BaseIO_mapTasks___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_EIO_mapTasks___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = l_BaseIO_mapTasks___redArg(x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l_EIO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_mk_io_user_error(x_6);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_mk_io_user_error(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_ctor_set_tag(x_2, 0);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_ofExcept___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_ofExcept(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_lazyPure___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_lazyPure___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_lazyPure(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_ms_now();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_nanos_now();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_io_get_random_bytes(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_sleep___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, lean_box(0));
x_4 = lean_dbg_sleep(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_IO_sleep(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
x_5 = lean_io_as_task(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_asTask___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_2);
x_6 = lean_io_as_task(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_asTask(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mapTask___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_io_map_task(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_IO_mapTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_io_map_task(x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_IO_mapTask(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_4, 0);
x_7 = lean_task_pure(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_bindTask___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_io_bind_task(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_IO_bindTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = lean_io_bind_task(x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_IO_bindTask(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_EIO_chainTask___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_IO_chainTask___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_EIO_chainTask___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l_IO_chainTask(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mapTasks___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_BaseIO_mapTasks___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_IO_mapTasks___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = l_BaseIO_mapTasks___redArg(x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_IO_mapTasks(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_io_check_canceled();
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_cancel(x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_TaskState_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_TaskState_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_IO_TaskState_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_waiting_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_TaskState_waiting_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_running_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_TaskState_running_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_TaskState_finished_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_TaskState_finished_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.waiting", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_instReprTaskState_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.running", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_instReprTaskState_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.TaskState.finished", 21, 21);
return x_1;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_instReprTaskState_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_IO_instReprTaskState_repr___closed__6;
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_IO_instReprTaskState_repr___closed__7;
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_IO_instReprTaskState_repr___closed__6;
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = l_IO_instReprTaskState_repr___closed__7;
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_IO_instReprTaskState_repr___closed__6;
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = l_IO_instReprTaskState_repr___closed__7;
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_instReprTaskState_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_IO_instReprTaskState_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_IO_instReprTaskState_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_IO_instReprTaskState_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_instReprTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instReprTaskState_repr___boxed), 2, 0);
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
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
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
x_3 = l_IO_TaskState_ctorIdx(x_1);
x_4 = l_IO_TaskState_ctorIdx(x_2);
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
x_4 = lean_unbox(x_2);
x_5 = l_IO_instDecidableEqTaskState(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_IO_TaskState_ctorIdx(x_1);
x_4 = l_IO_TaskState_ctorIdx(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_IO_instOrdTaskState_ord(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_instOrdTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instOrdTaskState_ord___boxed), 2, 0);
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
uint8_t x_3; 
x_3 = l_IO_instOrdTaskState_ord(x_1, x_2);
if (x_3 == 2)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_IO_instMinTaskState___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_instMinTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMinTaskState___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instMinTaskState() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instMinTaskState___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_IO_instOrdTaskState_ord(x_1, x_2);
if (x_3 == 2)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_IO_instMaxTaskState___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_instMaxTaskState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMaxTaskState___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instMaxTaskState() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instMaxTaskState___closed__0;
return x_1;
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
uint8_t x_4; lean_object* x_5; 
x_4 = lean_io_get_task_state(x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = lean_io_get_task_state(x_1);
if (x_3 == 2)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_hasFinished___redArg(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = lean_io_get_task_state(x_2);
if (x_4 == 2)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_IO_hasFinished(x_1, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO_waitAny___auto__1___closed__3;
x_2 = l_IO_waitAny___auto__1___closed__2;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO_waitAny___auto__1___closed__6;
x_2 = l_IO_waitAny___auto__1___closed__2;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_waitAny___auto__1___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO_waitAny___auto__1___closed__10;
x_2 = l_IO_waitAny___auto__1___closed__2;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_waitAny___auto__1___closed__10;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__12;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO_waitAny___auto__1___closed__15;
x_2 = l_IO_waitAny___auto__1___closed__14;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.zero_lt_succ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_waitAny___auto__1___closed__17;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__18;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_IO_waitAny___auto__1___closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero_lt_succ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__21;
x_2 = l_IO_waitAny___auto__1___closed__20;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_IO_waitAny___auto__1___closed__22;
x_3 = l_IO_waitAny___auto__1___closed__19;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__23;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO_waitAny___auto__1___closed__25;
x_2 = l_IO_waitAny___auto__1___closed__14;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_waitAny___auto__1___closed__27;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__28;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__29;
x_2 = l_IO_waitAny___auto__1___closed__26;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__30;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__31;
x_2 = l_IO_waitAny___auto__1___closed__9;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__32;
x_2 = l_IO_waitAny___auto__1___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__33;
x_2 = l_IO_waitAny___auto__1___closed__16;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__34;
x_2 = l_IO_waitAny___auto__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__35;
x_2 = l_IO_waitAny___auto__1___closed__11;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__36;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__37;
x_2 = l_IO_waitAny___auto__1___closed__9;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__38;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__39;
x_2 = l_IO_waitAny___auto__1___closed__7;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_waitAny___auto__1___closed__40;
x_2 = l_IO_waitAny___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_waitAny___auto__1___closed__41;
x_2 = l_IO_waitAny___auto__1___closed__4;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_IO_waitAny___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_waitAny___auto__1___closed__42;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_wait_any(x_2);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_waitAny___auto__1___closed__42;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_array_get_size(x_2);
x_7 = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 1;
x_10 = lean_task_map(x_7, x_4, x_8, x_9);
x_11 = lean_array_push(x_2, x_10);
x_1 = x_5;
x_2 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_IO_waitAny_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_IO_waitAny_x27___redArg___closed__0;
lean_inc(x_1);
x_4 = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(x_1, x_3);
x_5 = lean_io_wait_any(x_4);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_9 = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), x_1, x_1, x_7, x_3);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_1);
x_12 = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), x_1, x_1, x_10, x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_waitAny_x27___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_waitAny_x27___redArg(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_waitAny_x27(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_get_num_heartbeats();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_set_heartbeats(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_io_get_num_heartbeats();
x_4 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_5 = lean_io_set_heartbeats(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_addHeartbeats(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_FS_Mode_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_FS_Mode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_IO_FS_Mode_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_read_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_Mode_read_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_write_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_Mode_write_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_writeNew_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_Mode_writeNew_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_readWrite_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_Mode_readWrite_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_append_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_Mode_append_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instInhabitedStream_default___lam__0___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_instInhabitedStream_default___lam__0();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(size_t x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_instInhabitedStream_default___lam__1(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream_default___lam__2(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_instInhabitedStream_default___lam__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream_default___lam__4(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_IO_FS_instInhabitedStream_default___lam__5(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream_default___lam__5___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_IO_FS_instInhabitedStream_default___closed__5;
x_2 = l_IO_FS_instInhabitedStream_default___closed__4;
x_3 = l_IO_FS_instInhabitedStream_default___closed__3;
x_4 = l_IO_FS_instInhabitedStream_default___closed__2;
x_5 = l_IO_FS_instInhabitedStream_default___closed__1;
x_6 = l_IO_FS_instInhabitedStream_default___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream_default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedStream_default___closed__6;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedStream_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stderr();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdin(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdout(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stderr(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_2);
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_free_object(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_1 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_iterate___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_iterate___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_iterate(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lean_io_prim_handle_mk(x_1, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lean_io_prim_handle_lock(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lean_io_prim_handle_try_lock(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_unlock(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_io_prim_handle_is_tty(x_1);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_rewind(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_truncate(x_1);
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
x_5 = lean_io_prim_handle_read(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_file(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_dir(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_create_dir(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_rename(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_hard_link(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_create_tempfile();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_create_tempdir();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_prim_handle_mk(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_withFile___redArg(x_1, x_5, x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_prim_handle_mk(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
else
{
uint8_t x_9; 
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_IO_FS_withFile(x_1, x_2, x_6, x_4);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 10;
x_5 = lean_string_push(x_2, x_4);
x_6 = lean_io_prim_handle_put_str(x_1, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_putStrLn(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = 1024;
x_5 = lean_io_prim_handle_read(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_ByteArray_isEmpty(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_byte_array_size(x_2);
x_11 = lean_byte_array_size(x_7);
x_12 = lean_byte_array_copy_slice(x_7, x_9, x_2, x_10, x_11, x_8);
lean_dec(x_7);
x_2 = x_12;
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
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_ByteArray_isEmpty(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_byte_array_size(x_2);
x_18 = lean_byte_array_size(x_14);
x_19 = lean_byte_array_copy_slice(x_14, x_16, x_2, x_17, x_18, x_15);
lean_dec(x_14);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
}
}
else
{
lean_dec_ref(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEndInto(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_ByteArray_empty;
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readBinToEnd(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readBinToEnd(x_1);
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
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_string_validate_utf8(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = l_IO_FS_Handle_readToEnd___closed__1;
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_from_utf8_unchecked(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_get_line(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_22; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_43 = lean_string_length(x_5);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_string_utf8_byte_size(x_5);
lean_inc(x_5);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_String_Slice_Pos_prev_x3f(x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
uint32_t x_49; 
lean_dec_ref(x_47);
x_49 = 65;
x_22 = x_49;
goto block_42;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_String_Slice_Pos_get_x3f(x_47, x_50);
lean_dec(x_50);
lean_dec_ref(x_47);
if (lean_obj_tag(x_51) == 0)
{
uint32_t x_52; 
x_52 = 65;
x_22 = x_52;
goto block_42;
}
else
{
lean_object* x_53; uint32_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_unbox_uint32(x_53);
lean_dec(x_53);
x_22 = x_54;
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_2);
return x_55;
}
block_10:
{
lean_object* x_8; 
x_8 = lean_array_push(x_2, x_7);
x_2 = x_8;
goto _start;
}
block_21:
{
uint32_t x_15; uint8_t x_16; 
x_15 = 13;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_string_utf8_byte_size(x_12);
lean_inc(x_11);
lean_inc_ref(x_12);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_String_Slice_Pos_prevn(x_18, x_17, x_13);
lean_dec_ref(x_18);
x_20 = lean_string_utf8_extract(x_12, x_11, x_19);
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_12);
x_7 = x_20;
goto block_10;
}
}
block_42:
{
uint32_t x_23; uint8_t x_24; 
x_23 = 10;
x_24 = lean_uint32_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_push(x_2, x_5);
if (lean_is_scalar(x_6)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_6;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_string_utf8_byte_size(x_5);
lean_inc(x_5);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_String_Slice_Pos_prevn(x_30, x_29, x_27);
lean_dec_ref(x_30);
x_32 = lean_string_utf8_extract(x_5, x_28, x_31);
lean_dec(x_31);
lean_dec(x_5);
x_33 = lean_string_utf8_byte_size(x_32);
lean_inc_ref(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_String_Slice_Pos_prev_x3f(x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
uint32_t x_36; 
lean_dec_ref(x_34);
x_36 = 65;
x_11 = x_28;
x_12 = x_32;
x_13 = x_27;
x_14 = x_36;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_String_Slice_Pos_get_x3f(x_34, x_37);
lean_dec(x_37);
lean_dec_ref(x_34);
if (lean_obj_tag(x_38) == 0)
{
uint32_t x_39; 
x_39 = 65;
x_11 = x_28;
x_12 = x_32;
x_13 = x_27;
x_14 = x_39;
goto block_21;
}
else
{
lean_object* x_40; uint32_t x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_unbox_uint32(x_40);
lean_dec(x_40);
x_11 = x_28;
x_12 = x_32;
x_13 = x_27;
x_14 = x_41;
goto block_21;
}
}
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_4);
if (x_56 == 0)
{
return x_4;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_4, 0);
lean_inc(x_57);
lean_dec(x_4);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_IO_FS_Handle_lines___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_Handle_lines___closed__0;
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_lines(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_io_prim_handle_mk(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_IO_FS_Handle_lines(x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_lines(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_io_prim_handle_mk(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_io_prim_handle_write(x_6, x_2);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeBinFile(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_io_prim_handle_mk(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_io_prim_handle_put_str(x_6, x_2);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = 10;
x_6 = lean_string_push(x_2, x_5);
x_7 = lean_apply_2(x_4, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_putStrLn(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("root", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_2 = l_IO_FS_instReprDirEntry_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fileName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_6 = l_IO_FS_instReprDirEntry_repr___redArg___closed__6;
x_7 = l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_IO_FS_instReprDirEntry_repr___redArg___closed__9;
x_10 = l_String_quote(x_3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_12 = l_Repr_addAppParen(x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_IO_FS_instReprDirEntry_repr___redArg___closed__13;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
x_25 = l_String_quote(x_4);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_14);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
x_31 = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_14);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_40 = l_IO_FS_instReprDirEntry_repr___redArg___closed__6;
x_41 = l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_IO_FS_instReprDirEntry_repr___redArg___closed__9;
x_44 = l_String_quote(x_37);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Repr_addAppParen(x_46, x_42);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = 0;
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_IO_FS_instReprDirEntry_repr___redArg___closed__13;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_39);
x_59 = l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
x_60 = l_String_quote(x_38);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_49);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
x_66 = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_68 = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_49);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprDirEntry_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprDirEntry_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instReprDirEntry_repr___boxed), 2, 0);
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
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_FS_FileType_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_FS_FileType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_IO_FS_FileType_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_dir_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_FileType_dir_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_file_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_FileType_file_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_symlink_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_FileType_symlink_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_FileType_other_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_FS_FileType_other_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.dir", 18, 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprFileType_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.file", 19, 19);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprFileType_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.symlink", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprFileType_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.FS.FileType.other", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprFileType_repr___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; 
switch (x_1) {
case 0:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_IO_instReprTaskState_repr___closed__6;
x_3 = x_33;
goto block_9;
}
else
{
lean_object* x_34; 
x_34 = l_IO_instReprTaskState_repr___closed__7;
x_3 = x_34;
goto block_9;
}
}
case 1:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_IO_instReprTaskState_repr___closed__6;
x_10 = x_37;
goto block_16;
}
else
{
lean_object* x_38; 
x_38 = l_IO_instReprTaskState_repr___closed__7;
x_10 = x_38;
goto block_16;
}
}
case 2:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_IO_instReprTaskState_repr___closed__6;
x_17 = x_41;
goto block_23;
}
else
{
lean_object* x_42; 
x_42 = l_IO_instReprTaskState_repr___closed__7;
x_17 = x_42;
goto block_23;
}
}
default: 
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_IO_instReprTaskState_repr___closed__6;
x_24 = x_45;
goto block_30;
}
else
{
lean_object* x_46; 
x_46 = l_IO_instReprTaskState_repr___closed__7;
x_24 = x_46;
goto block_30;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_FS_instReprFileType_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_IO_FS_instReprFileType_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_IO_FS_instReprFileType_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_IO_FS_instReprFileType_repr___closed__7;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_IO_FS_instReprFileType_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instReprFileType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instReprFileType_repr___boxed), 2, 0);
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
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_IO_FS_FileType_ctorIdx(x_1);
x_4 = l_IO_FS_FileType_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_IO_FS_instBEqFileType_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instBEqFileType_beq___boxed), 2, 0);
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
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprSystemTime_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprSystemTime_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_2 = l_IO_FS_instReprSystemTime_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nsec", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprSystemTime_repr___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_4 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_5 = l_IO_FS_instReprSystemTime_repr___redArg___closed__3;
x_6 = l_IO_FS_instReprSystemTime_repr___redArg___closed__4;
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_IO_FS_instReprSystemTime_repr___redArg___closed__7;
x_36 = lean_int_dec_lt(x_2, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Int_repr(x_2);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_7 = x_38;
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Int_repr(x_2);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Repr_addAppParen(x_40, x_34);
x_7 = x_41;
goto block_33;
}
block_33:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = 0;
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_IO_FS_instReprSystemTime_repr___redArg___closed__6;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
x_20 = lean_uint32_to_nat(x_3);
x_21 = l_Nat_reprFast(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_9);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
x_27 = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_9);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_instReprSystemTime_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprSystemTime_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprSystemTime_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instReprSystemTime_repr___boxed), 2, 0);
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
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_FS_instBEqSystemTime_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instBEqSystemTime_beq___boxed), 2, 0);
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
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_uint32_dec_lt(x_4, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_uint32_dec_eq(x_4, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_FS_instOrdSystemTime_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instOrdSystemTime_ord___boxed), 2, 0);
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
static uint32_t _init_l_IO_FS_instInhabitedSystemTime_default___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instInhabitedSystemTime_default___closed__0;
x_2 = l_IO_FS_instReprSystemTime_repr___redArg___closed__7;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedSystemTime_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedSystemTime_default;
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
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("accessed", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprMetadata_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprMetadata_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_2 = l_IO_FS_instReprMetadata_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("modified", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprMetadata_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("byteSize", 8, 8);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprMetadata_repr___redArg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type", 4, 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_instReprMetadata_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_6 = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
x_7 = l_IO_FS_instReprMetadata_repr___redArg___closed__3;
x_8 = l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_IO_FS_instReprSystemTime_repr___redArg(x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_IO_FS_instReprMetadata_repr___redArg___closed__5;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_22 = l_IO_FS_instReprSystemTime_repr___redArg(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_12);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_28 = l_IO_FS_instReprMetadata_repr___redArg___closed__7;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
x_31 = lean_uint64_to_nat(x_4);
x_32 = l_Nat_reprFast(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_12);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_15);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_17);
x_39 = l_IO_FS_instReprMetadata_repr___redArg___closed__9;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
x_42 = l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
x_43 = l_IO_FS_instReprFileType_repr(x_5, x_9);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_12);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
x_48 = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_12);
return x_53;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_instReprMetadata_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprMetadata_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instReprMetadata_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instReprMetadata_repr___boxed), 2, 0);
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
x_3 = lean_io_read_dir(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_symlink_metadata(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 8);
lean_dec(x_4);
x_6 = 0;
x_7 = l_IO_FS_instBEqFileType_beq(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_FilePath_isDir(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_3);
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_FilePath_pathExists(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_uget(x_4, x_6);
x_21 = l_IO_FS_DirEntry_path(x_20);
lean_inc_ref(x_21);
x_22 = lean_array_push(x_8, x_21);
x_23 = lean_io_metadata(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 8);
lean_dec(x_24);
switch (x_25) {
case 2:
{
lean_object* x_26; 
x_26 = lean_io_realpath(x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_System_FilePath_isDir(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_10 = x_1;
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_29; 
lean_inc_ref(x_2);
lean_inc_ref(x_3);
x_29 = lean_apply_2(x_2, x_3, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_27);
x_10 = x_1;
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; 
lean_inc_ref(x_2);
x_32 = l___private_Init_System_IO_0__System_FilePath_walkDir_go(x_2, x_27, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_10 = x_1;
x_11 = x_34;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_32;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec_ref(x_22);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
case 0:
{
lean_object* x_41; 
lean_inc_ref(x_2);
x_41 = l___private_Init_System_IO_0__System_FilePath_walkDir_go(x_2, x_21, x_22);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_10 = x_1;
x_11 = x_43;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_41;
}
}
default: 
{
lean_dec_ref(x_21);
x_10 = x_1;
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_21);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_45) == 11)
{
lean_free_object(x_23);
lean_dec_ref(x_45);
x_10 = x_1;
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_22);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_23;
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_23, 0);
lean_inc(x_46);
lean_dec(x_23);
if (lean_obj_tag(x_46) == 11)
{
lean_dec_ref(x_46);
x_10 = x_1;
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_47; 
lean_dec_ref(x_22);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; 
lean_free_object(x_5);
x_11 = lean_io_read_dir(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(x_13, x_1, x_2, x_12, x_14, x_15, x_13, x_3);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_13);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
return x_16;
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_io_read_dir(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_box(0);
x_39 = lean_array_size(x_37);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(x_38, x_1, x_2, x_37, x_39, x_40, x_38, x_3);
lean_dec(x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_44);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
return x_41;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
lean_dec(x_5);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_System_IO_0__System_FilePath_walkDir_go(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_Handle_lines___closed__0;
x_5 = l___private_Init_System_IO_0__System_FilePath_walkDir_go(x_2, x_1, x_4);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_System_FilePath_walkDir(x_1, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = 0;
x_6 = lean_io_prim_handle_mk(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 0;
x_11 = lean_usize_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_IO_FS_readBinFile___closed__0;
x_13 = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(x_7, x_12);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_io_prim_handle_read(x_7, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(x_7, x_15);
lean_dec(x_7);
return x_16;
}
else
{
lean_dec(x_7);
return x_14;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1);
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
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_string_validate_utf8(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_15 = l_IO_FS_readFile___closed__0;
x_16 = lean_string_append(x_15, x_1);
x_17 = l_IO_FS_readFile___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_string_from_utf8_unchecked(x_13);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_withStdin___redArg___lam__0(x_1);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
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
static lean_object* _init_l_IO_withStdin___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = l_IO_withStdin___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = l_IO_withStdin___redArg___closed__0;
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = l_IO_withStdin___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_stdout();
x_5 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_2(x_5, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_print___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_print___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_print(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_println___redArg___closed__0;
x_5 = lean_apply_1(x_1, x_2);
x_6 = 10;
x_7 = lean_string_push(x_5, x_6);
x_8 = l_IO_print___redArg(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_println___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_println___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_println(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_stderr();
x_5 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_2(x_5, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_eprint___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprint___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprint(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_IO_println___redArg___closed__0;
x_5 = lean_apply_1(x_1, x_2);
x_6 = 10;
x_7 = lean_string_push(x_5, x_6);
x_8 = l_IO_eprint___redArg(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_eprintln___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprintln___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprintln(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_eprint(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_eprintln(x_1);
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
LEAN_EXPORT lean_object* l_IO_appDir() {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_System_FilePath_parent(x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_free_object(x_2);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_io_realpath(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_8 = l_IO_appDir___closed__0;
x_9 = lean_string_append(x_8, x_4);
lean_dec(x_4);
x_10 = l_IO_appDir___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_mk_io_user_error(x_11);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_13);
x_14 = l_System_FilePath_parent(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_io_realpath(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_17 = l_IO_appDir___closed__0;
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
x_19 = l_IO_appDir___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_mk_io_user_error(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_appDir();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_15; 
x_15 = l_System_FilePath_isDir(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_IO_FS_createDirAll(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_3 = lean_box(0);
goto block_14;
}
else
{
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_dec(x_16);
x_3 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
block_14:
{
lean_object* x_4; 
x_4 = lean_io_create_dir(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_System_FilePath_isDir(x_1);
lean_dec_ref(x_1);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_System_FilePath_isDir(x_1);
lean_dec_ref(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
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
x_3 = l_IO_FS_createDirAll(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = l_IO_FS_DirEntry_path(x_15);
x_17 = lean_io_symlink_metadata(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 8);
lean_dec(x_18);
x_20 = 0;
x_21 = l_IO_FS_instBEqFileType_beq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_io_remove_file(x_16);
lean_dec_ref(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_7 = x_1;
x_8 = lean_box(0);
goto block_12;
}
else
{
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_IO_FS_removeDirAll(x_16);
lean_dec_ref(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_7 = x_1;
x_8 = lean_box(0);
goto block_12;
}
else
{
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_16);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_box(0);
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(x_5, x_4, x_6, x_7, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = lean_io_remove_dir(x_1);
return x_9;
}
else
{
return x_8;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_removeDirAll(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
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
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_IO_withStdin___redArg___closed__0;
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
lean_dec_ref(x_1);
lean_inc_ref(x_6);
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_IO_withStdin___redArg___closed__0;
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
x_2 = lean_io_process_get_current_dir();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_set_current_dir(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_io_process_get_pid();
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_Process_Stdio_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Process_Stdio_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_IO_Process_Stdio_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Process_Stdio_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_IO_Process_Stdio_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Process_Stdio_piped_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_Process_Stdio_piped_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Process_Stdio_inherit_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_Process_Stdio_inherit_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Process_Stdio_null_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_IO_Process_Stdio_null_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_spawn(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_wait(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_try_wait(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_kill(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_take_stdin(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_io_process_child_pid(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* x_1) {
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
x_6 = lean_mk_io_user_error(x_5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00IO_Process_output_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Process_output___lam__0(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_Process_output___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_Process_output___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = l_IO_Process_output___closed__1;
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
lean_ctor_set(x_1, 0, x_37);
x_40 = lean_io_process_spawn(x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_io_process_child_take_stdin(x_37, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_io_prim_handle_put_str(x_44, x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_46);
x_47 = lean_io_prim_handle_flush(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_4 = x_45;
x_5 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_44);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_ctor_get(x_1, 3);
x_63 = lean_ctor_get(x_1, 4);
x_64 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_66, 0, x_37);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*5 + 1, x_65);
x_67 = lean_io_process_spawn(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_io_process_child_take_stdin(x_37, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_io_prim_handle_put_str(x_71, x_36);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec_ref(x_73);
x_74 = lean_io_prim_handle_flush(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_74);
x_4 = x_72;
x_5 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec(x_71);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_82 = x_69;
} else {
 lean_dec_ref(x_69);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_67, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_85 = x_67;
} else {
 lean_dec_ref(x_67);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_IO_Process_output___closed__0;
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_1, 0);
lean_dec(x_89);
lean_ctor_set(x_1, 0, x_87);
x_90 = lean_io_process_spawn(x_1);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_4 = x_91;
x_5 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_1, 1);
x_96 = lean_ctor_get(x_1, 2);
x_97 = lean_ctor_get(x_1, 3);
x_98 = lean_ctor_get(x_1, 4);
x_99 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_101, 0, x_87);
lean_ctor_set(x_101, 1, x_95);
lean_ctor_set(x_101, 2, x_96);
lean_ctor_set(x_101, 3, x_97);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*5, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*5 + 1, x_100);
x_102 = lean_io_process_spawn(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_4 = x_103;
x_5 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
}
block_35:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_unsigned_to_nat(9u);
x_10 = lean_io_as_task(x_8, x_9);
x_11 = l_IO_FS_Handle_readToEnd(x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_IO_Process_output___closed__0;
x_14 = lean_io_process_child_wait(x_13, x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_task_get_own(x_10);
x_17 = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = lean_unbox_uint32(x_15);
lean_dec(x_15);
lean_ctor_set_uint32(x_20, sizeof(void*)*2, x_21);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
x_24 = lean_unbox_uint32(x_15);
lean_dec(x_15);
lean_ctor_set_uint32(x_23, sizeof(void*)*2, x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec_ref(x_10);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_10);
lean_dec_ref(x_4);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Process_output(x_1, x_2);
lean_dec(x_2);
return x_4;
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
lean_object* x_4; 
lean_inc_ref(x_1);
x_4 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get_uint32(x_6, sizeof(void*)*2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = 0;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = l_IO_Process_run___closed__0;
x_14 = lean_string_append(x_13, x_12);
lean_dec_ref(x_12);
x_15 = l_IO_Process_run___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_uint32_to_nat(x_7);
x_18 = l_Nat_reprFast(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec_ref(x_18);
x_20 = l_IO_Process_run___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_9);
lean_dec_ref(x_9);
x_23 = lean_mk_io_user_error(x_22);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
}
else
{
lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get_uint32(x_24, sizeof(void*)*2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_27);
lean_dec(x_24);
x_28 = 0;
x_29 = lean_uint32_dec_eq(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_26);
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = l_IO_Process_run___closed__0;
x_32 = lean_string_append(x_31, x_30);
lean_dec_ref(x_30);
x_33 = l_IO_Process_run___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_uint32_to_nat(x_25);
x_36 = l_Nat_reprFast(x_35);
x_37 = lean_string_append(x_34, x_36);
lean_dec_ref(x_36);
x_38 = l_IO_Process_run___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_27);
lean_dec_ref(x_27);
x_41 = lean_mk_io_user_error(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec_ref(x_27);
lean_dec_ref(x_1);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_26);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_4);
if (x_44 == 0)
{
return x_4;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Process_run(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lean_io_exit(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lean_io_force_exit(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_io_get_tid();
x_3 = lean_box_uint64(x_2);
return x_3;
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
x_5 = lean_uint32_lor(x_3, x_4);
x_6 = lean_uint32_lor(x_2, x_5);
return x_6;
}
block_15:
{
if (x_10 == 0)
{
uint32_t x_13; 
x_13 = 0;
x_2 = x_11;
x_3 = x_12;
x_4 = x_13;
goto block_7;
}
else
{
uint32_t x_14; 
x_14 = 1;
x_2 = x_11;
x_3 = x_12;
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
x_5 = lean_chmod(x_1, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_IO_FileRight_flags(x_2);
x_5 = lean_chmod(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_setAccessRights(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_instMonadLiftSTRealWorldBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_IO_instMonadLiftSTRealWorldBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instMonadLiftSTRealWorldBaseIO___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_mkRef___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_st_mk_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mkRef(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new() {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_st_mk_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_CancelToken_new();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_st_ref_set(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_CancelToken_set(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_IO_CancelToken_isSet(x_1);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_io_cancel_token_is_set(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_usize_to_nat(x_2);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_inc(x_7);
x_10 = l_ByteArray_extract(x_6, x_7, x_9);
lean_dec(x_9);
x_11 = lean_byte_array_size(x_10);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_12);
x_13 = lean_st_ref_set(x_1, x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_usize_to_nat(x_2);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_inc(x_16);
x_19 = l_ByteArray_extract(x_15, x_16, x_18);
lean_dec(x_18);
x_20 = lean_byte_array_size(x_19);
x_21 = lean_nat_add(x_16, x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_st_ref_set(x_1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofBuffer___lam__0(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_byte_array_size(x_2);
x_10 = 0;
lean_inc(x_7);
x_11 = lean_byte_array_copy_slice(x_2, x_8, x_6, x_7, x_9, x_10);
x_12 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
x_13 = lean_st_ref_set(x_1, x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_byte_array_size(x_2);
x_19 = 0;
lean_inc(x_16);
x_20 = lean_byte_array_copy_slice(x_2, x_17, x_15, x_16, x_18, x_19);
x_21 = lean_nat_add(x_16, x_18);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_st_ref_set(x_1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___lam__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_to_utf8(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_byte_array_size(x_8);
x_11 = 0;
lean_inc(x_7);
x_12 = lean_byte_array_copy_slice(x_8, x_9, x_6, x_7, x_10, x_11);
lean_dec_ref(x_8);
x_13 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_12);
x_14 = lean_st_ref_set(x_1, x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_string_to_utf8(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_byte_array_size(x_18);
x_21 = 0;
lean_inc(x_17);
x_22 = lean_byte_array_copy_slice(x_18, x_19, x_16, x_17, x_20, x_21);
lean_dec_ref(x_18);
x_23 = lean_nat_add(x_17, x_20);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___lam__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_byte_array_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
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
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_17; 
x_3 = lean_st_ref_take(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
lean_inc(x_5);
x_17 = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_byte_array_size(x_4);
x_7 = x_18;
goto block_16;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_byte_array_get(x_4, x_19);
x_21 = 0;
x_22 = lean_uint8_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_19, x_23);
lean_dec(x_19);
x_7 = x_24;
goto block_16;
}
else
{
x_7 = x_19;
goto block_16;
}
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_ByteArray_extract(x_4, x_5, x_7);
if (lean_is_scalar(x_6)) {
 x_9 = lean_alloc_ctor(0, 2, 0);
} else {
 x_9 = x_6;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_st_ref_set(x_1, x_9);
x_11 = lean_string_validate_utf8(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_8);
x_12 = l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_from_utf8_unchecked(x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___lam__3(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___lam__4(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_ofBuffer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__4___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
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
x_6 = l_IO_FS_Stream_ofBuffer___closed__0;
x_7 = l_IO_FS_instInhabitedStream_default___closed__5;
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1024;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1;
lean_inc_ref(x_4);
x_6 = lean_apply_2(x_4, x_5, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_ByteArray_isEmpty(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_byte_array_size(x_2);
x_12 = lean_byte_array_size(x_8);
x_13 = lean_byte_array_copy_slice(x_8, x_10, x_2, x_11, x_12, x_9);
lean_dec(x_8);
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_ByteArray_isEmpty(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_byte_array_size(x_2);
x_19 = lean_byte_array_size(x_15);
x_20 = lean_byte_array_copy_slice(x_15, x_17, x_2, x_18, x_19, x_16);
lean_dec(x_15);
x_2 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readBinToEndInto(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_ByteArray_empty;
x_4 = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readBinToEnd(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readToEnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tried to read from stream containing non UTF-8 data.", 52, 52);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readToEnd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readToEnd___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readBinToEnd(x_1);
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
x_7 = l_IO_FS_Stream_readToEnd___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
x_8 = lean_string_from_utf8_unchecked(x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_string_validate_utf8(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = l_IO_FS_Stream_readToEnd___closed__1;
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_from_utf8_unchecked(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readToEnd(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
x_5 = lean_apply_1(x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint32_t x_23; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_44 = lean_string_length(x_6);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_string_utf8_byte_size(x_6);
lean_inc(x_6);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_String_Slice_Pos_prev_x3f(x_48, x_47);
if (lean_obj_tag(x_49) == 0)
{
uint32_t x_50; 
lean_dec_ref(x_48);
x_50 = 65;
x_23 = x_50;
goto block_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_String_Slice_Pos_get_x3f(x_48, x_51);
lean_dec(x_51);
lean_dec_ref(x_48);
if (lean_obj_tag(x_52) == 0)
{
uint32_t x_53; 
x_53 = 65;
x_23 = x_53;
goto block_43;
}
else
{
lean_object* x_54; uint32_t x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_unbox_uint32(x_54);
lean_dec(x_54);
x_23 = x_55;
goto block_43;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_2);
return x_56;
}
block_11:
{
lean_object* x_9; 
x_9 = lean_array_push(x_2, x_8);
x_2 = x_9;
goto _start;
}
block_22:
{
uint32_t x_16; uint8_t x_17; 
x_16 = 13;
x_17 = lean_uint32_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_string_utf8_byte_size(x_12);
lean_inc(x_14);
lean_inc_ref(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_String_Slice_Pos_prevn(x_19, x_18, x_13);
lean_dec_ref(x_19);
x_21 = lean_string_utf8_extract(x_12, x_14, x_20);
lean_dec(x_20);
lean_dec(x_14);
lean_dec_ref(x_12);
x_8 = x_21;
goto block_11;
}
}
block_43:
{
uint32_t x_24; uint8_t x_25; 
x_24 = 10;
x_25 = lean_uint32_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_1);
x_26 = lean_array_push(x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_7;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_7);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_string_utf8_byte_size(x_6);
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_String_Slice_Pos_prevn(x_31, x_30, x_28);
lean_dec_ref(x_31);
x_33 = lean_string_utf8_extract(x_6, x_29, x_32);
lean_dec(x_32);
lean_dec(x_6);
x_34 = lean_string_utf8_byte_size(x_33);
lean_inc_ref(x_33);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_String_Slice_Pos_prev_x3f(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
uint32_t x_37; 
lean_dec_ref(x_35);
x_37 = 65;
x_12 = x_33;
x_13 = x_28;
x_14 = x_29;
x_15 = x_37;
goto block_22;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_String_Slice_Pos_get_x3f(x_35, x_38);
lean_dec(x_38);
lean_dec_ref(x_35);
if (lean_obj_tag(x_39) == 0)
{
uint32_t x_40; 
x_40 = 65;
x_12 = x_33;
x_13 = x_28;
x_14 = x_29;
x_15 = x_40;
goto block_22;
}
else
{
lean_object* x_41; uint32_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_12 = x_33;
x_13 = x_28;
x_14 = x_29;
x_15 = x_42;
goto block_22;
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
return x_5;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_5, 0);
lean_inc(x_58);
lean_dec(x_5);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_Handle_lines___closed__0;
x_4 = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_lines(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_ref_get(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_withIsolatedStreams___redArg___lam__0(x_1);
lean_dec(x_1);
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
x_1 = lean_mk_string_unchecked("Init.Data.String.Basic", 22, 22);
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
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(185u);
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
lean_inc_ref(x_8);
lean_dec_ref(x_3);
x_9 = lean_string_validate_utf8(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_8);
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
x_6 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
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
lean_inc_ref(x_13);
lean_inc(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l_IO_withStderr___redArg(x_5, x_6, x_2, x_13, x_8);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_IO_withStdout___redArg(x_5, x_6, x_2, x_13, x_14);
x_16 = l_IO_withStdin___redArg(x_5, x_6, x_2, x_12, x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
x_11 = l_IO_FS_withIsolatedStreams___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l_IO_FS_withIsolatedStreams___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_ByteArray_empty;
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
x_2 = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
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
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_IO_FS_withIsolatedStreams___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_IO_FS_withIsolatedStreams(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termPrintln!__", 14, 14);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("println! ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_____00__closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_termPrintln_x21_____00__closed__11;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_____00__closed__12;
x_2 = l_termPrintln_x21_____00__closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_____00__closed__12;
x_2 = l_termPrintln_x21_____00__closed__13;
x_3 = l_termPrintln_x21_____00__closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_____00__closed__14;
x_2 = l_termPrintln_x21_____00__closed__5;
x_3 = l_termPrintln_x21_____00__closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_____00__closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_____00__closed__15;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_termPrintln_x21_____00__closed__1;
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
x_1 = l_termPrintln_x21_____00__closed__16;
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
x_2 = l_IO_waitAny___auto__1___closed__14;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygienicLParen", 14, 14);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
x_2 = l_IO_waitAny___auto__1___closed__14;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("System", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO.println", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IO", 2, 2);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("println", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
x_2 = l_IO_waitAny___auto__1___closed__14;
x_3 = l_IO_waitAny___auto__1___closed__1;
x_4 = l_IO_waitAny___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termS!_", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42() {
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
x_4 = l_termPrintln_x21_____00__closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_SourceInfo_fromRef(x_14, x_11);
lean_dec(x_14);
x_16 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_17 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
x_18 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_21 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
x_22 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
x_23 = l_Lean_addMacroScope(x_12, x_22, x_13);
x_24 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
lean_inc(x_15);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_15);
x_26 = l_Lean_Syntax_node1(x_15, x_20, x_25);
lean_inc(x_15);
x_27 = l_Lean_Syntax_node2(x_15, x_17, x_19, x_26);
x_28 = l_IO_waitAny___auto__1___closed__16;
x_29 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_30 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_13);
lean_inc(x_12);
x_31 = l_Lean_addMacroScope(x_12, x_30, x_13);
x_32 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_15);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_IO_waitAny___auto__1___closed__9;
lean_inc(x_15);
x_35 = l_Lean_Syntax_node1(x_15, x_34, x_9);
lean_inc(x_15);
x_36 = l_Lean_Syntax_node2(x_15, x_28, x_33, x_35);
x_37 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
lean_inc(x_15);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_40 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
lean_inc(x_13);
lean_inc(x_12);
x_41 = l_Lean_addMacroScope(x_12, x_40, x_13);
x_42 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
lean_inc(x_15);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
x_44 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
x_45 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_46 = l_Lean_addMacroScope(x_12, x_45, x_13);
x_47 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
lean_inc(x_15);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc(x_15);
x_49 = l_Lean_Syntax_node1(x_15, x_34, x_48);
lean_inc(x_15);
x_50 = l_Lean_Syntax_node2(x_15, x_28, x_43, x_49);
lean_inc(x_15);
x_51 = l_Lean_Syntax_node1(x_15, x_34, x_50);
x_52 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
lean_inc(x_15);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_15);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Syntax_node5(x_15, x_16, x_27, x_36, x_38, x_51, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 5);
lean_inc(x_58);
lean_dec_ref(x_2);
x_59 = 0;
x_60 = l_Lean_SourceInfo_fromRef(x_58, x_59);
lean_dec(x_58);
x_61 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_62 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
x_63 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
lean_inc(x_60);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_66 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
x_67 = lean_box(0);
lean_inc(x_57);
lean_inc(x_56);
x_68 = l_Lean_addMacroScope(x_56, x_67, x_57);
x_69 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
lean_inc(x_60);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
lean_inc(x_60);
x_71 = l_Lean_Syntax_node1(x_60, x_65, x_70);
lean_inc(x_60);
x_72 = l_Lean_Syntax_node2(x_60, x_62, x_64, x_71);
x_73 = l_IO_waitAny___auto__1___closed__16;
x_74 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_75 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_57);
lean_inc(x_56);
x_76 = l_Lean_addMacroScope(x_56, x_75, x_57);
x_77 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_60);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
x_79 = l_IO_waitAny___auto__1___closed__9;
x_80 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
x_81 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
x_82 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
lean_inc(x_60);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_60);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_60);
x_84 = l_Lean_Syntax_node2(x_60, x_81, x_83, x_9);
x_85 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
lean_inc(x_60);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_60);
lean_ctor_set(x_86, 1, x_85);
lean_inc_ref(x_86);
lean_inc(x_72);
lean_inc(x_60);
x_87 = l_Lean_Syntax_node3(x_60, x_80, x_72, x_84, x_86);
lean_inc(x_60);
x_88 = l_Lean_Syntax_node1(x_60, x_79, x_87);
lean_inc(x_60);
x_89 = l_Lean_Syntax_node2(x_60, x_73, x_78, x_88);
x_90 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
lean_inc(x_60);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_60);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_93 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
lean_inc(x_57);
lean_inc(x_56);
x_94 = l_Lean_addMacroScope(x_56, x_93, x_57);
x_95 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
lean_inc(x_60);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_60);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_95);
x_97 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
x_98 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_99 = l_Lean_addMacroScope(x_56, x_98, x_57);
x_100 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
lean_inc(x_60);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_60);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
lean_inc(x_60);
x_102 = l_Lean_Syntax_node1(x_60, x_79, x_101);
lean_inc(x_60);
x_103 = l_Lean_Syntax_node2(x_60, x_73, x_96, x_102);
lean_inc(x_60);
x_104 = l_Lean_Syntax_node1(x_60, x_79, x_103);
x_105 = l_Lean_Syntax_node5(x_60, x_61, x_72, x_89, x_91, x_104, x_86);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_3);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_mark_multi_threaded(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_mark_persistent(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_runtime_forget(x_2);
return x_4;
}
}
lean_object* initialize_Init_System_IOError(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_RealWorld_nonemptyType = _init_l_IO_RealWorld_nonemptyType();
l_instMonadBaseIO___closed__0 = _init_l_instMonadBaseIO___closed__0();
lean_mark_persistent(l_instMonadBaseIO___closed__0);
l_instMonadBaseIO = _init_l_instMonadBaseIO();
lean_mark_persistent(l_instMonadBaseIO);
l_instMonadFinallyBaseIO___closed__0 = _init_l_instMonadFinallyBaseIO___closed__0();
lean_mark_persistent(l_instMonadFinallyBaseIO___closed__0);
l_instMonadFinallyBaseIO = _init_l_instMonadFinallyBaseIO();
lean_mark_persistent(l_instMonadFinallyBaseIO);
l_instMonadAttachBaseIO___closed__0 = _init_l_instMonadAttachBaseIO___closed__0();
lean_mark_persistent(l_instMonadAttachBaseIO___closed__0);
l_instMonadAttachBaseIO = _init_l_instMonadAttachBaseIO();
lean_mark_persistent(l_instMonadAttachBaseIO);
l_instMonadLiftBaseIOEIO___closed__0 = _init_l_instMonadLiftBaseIOEIO___closed__0();
lean_mark_persistent(l_instMonadLiftBaseIOEIO___closed__0);
l_instMonadEIO___closed__0 = _init_l_instMonadEIO___closed__0();
lean_mark_persistent(l_instMonadEIO___closed__0);
l_instMonadFinallyEIO___closed__0 = _init_l_instMonadFinallyEIO___closed__0();
lean_mark_persistent(l_instMonadFinallyEIO___closed__0);
l_instMonadAttachEIO___closed__0 = _init_l_instMonadAttachEIO___closed__0();
lean_mark_persistent(l_instMonadAttachEIO___closed__0);
l_instMonadExceptOfEIO___closed__0 = _init_l_instMonadExceptOfEIO___closed__0();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__0);
l_instOrElseEIO___closed__0 = _init_l_instOrElseEIO___closed__0();
lean_mark_persistent(l_instOrElseEIO___closed__0);
l_instOrElseEIO___closed__1 = _init_l_instOrElseEIO___closed__1();
lean_mark_persistent(l_instOrElseEIO___closed__1);
l_IO_instInhabitedTaskState_default = _init_l_IO_instInhabitedTaskState_default();
l_IO_instInhabitedTaskState = _init_l_IO_instInhabitedTaskState();
l_IO_instReprTaskState_repr___closed__0 = _init_l_IO_instReprTaskState_repr___closed__0();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__0);
l_IO_instReprTaskState_repr___closed__1 = _init_l_IO_instReprTaskState_repr___closed__1();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__1);
l_IO_instReprTaskState_repr___closed__2 = _init_l_IO_instReprTaskState_repr___closed__2();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__2);
l_IO_instReprTaskState_repr___closed__3 = _init_l_IO_instReprTaskState_repr___closed__3();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__3);
l_IO_instReprTaskState_repr___closed__4 = _init_l_IO_instReprTaskState_repr___closed__4();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__4);
l_IO_instReprTaskState_repr___closed__5 = _init_l_IO_instReprTaskState_repr___closed__5();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__5);
l_IO_instReprTaskState_repr___closed__6 = _init_l_IO_instReprTaskState_repr___closed__6();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__6);
l_IO_instReprTaskState_repr___closed__7 = _init_l_IO_instReprTaskState_repr___closed__7();
lean_mark_persistent(l_IO_instReprTaskState_repr___closed__7);
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
l_IO_instMinTaskState___closed__0 = _init_l_IO_instMinTaskState___closed__0();
lean_mark_persistent(l_IO_instMinTaskState___closed__0);
l_IO_instMinTaskState = _init_l_IO_instMinTaskState();
lean_mark_persistent(l_IO_instMinTaskState);
l_IO_instMaxTaskState___closed__0 = _init_l_IO_instMaxTaskState___closed__0();
lean_mark_persistent(l_IO_instMaxTaskState___closed__0);
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
l_IO_waitAny___auto__1___closed__0 = _init_l_IO_waitAny___auto__1___closed__0();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__0);
l_IO_waitAny___auto__1___closed__1 = _init_l_IO_waitAny___auto__1___closed__1();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__1);
l_IO_waitAny___auto__1___closed__2 = _init_l_IO_waitAny___auto__1___closed__2();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__2);
l_IO_waitAny___auto__1___closed__3 = _init_l_IO_waitAny___auto__1___closed__3();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__3);
l_IO_waitAny___auto__1___closed__4 = _init_l_IO_waitAny___auto__1___closed__4();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__4);
l_IO_waitAny___auto__1___closed__5 = _init_l_IO_waitAny___auto__1___closed__5();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__5);
l_IO_waitAny___auto__1___closed__6 = _init_l_IO_waitAny___auto__1___closed__6();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__6);
l_IO_waitAny___auto__1___closed__7 = _init_l_IO_waitAny___auto__1___closed__7();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__7);
l_IO_waitAny___auto__1___closed__8 = _init_l_IO_waitAny___auto__1___closed__8();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__8);
l_IO_waitAny___auto__1___closed__9 = _init_l_IO_waitAny___auto__1___closed__9();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__9);
l_IO_waitAny___auto__1___closed__10 = _init_l_IO_waitAny___auto__1___closed__10();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__10);
l_IO_waitAny___auto__1___closed__11 = _init_l_IO_waitAny___auto__1___closed__11();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__11);
l_IO_waitAny___auto__1___closed__12 = _init_l_IO_waitAny___auto__1___closed__12();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__12);
l_IO_waitAny___auto__1___closed__13 = _init_l_IO_waitAny___auto__1___closed__13();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__13);
l_IO_waitAny___auto__1___closed__14 = _init_l_IO_waitAny___auto__1___closed__14();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__14);
l_IO_waitAny___auto__1___closed__15 = _init_l_IO_waitAny___auto__1___closed__15();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__15);
l_IO_waitAny___auto__1___closed__16 = _init_l_IO_waitAny___auto__1___closed__16();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__16);
l_IO_waitAny___auto__1___closed__17 = _init_l_IO_waitAny___auto__1___closed__17();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__17);
l_IO_waitAny___auto__1___closed__18 = _init_l_IO_waitAny___auto__1___closed__18();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__18);
l_IO_waitAny___auto__1___closed__19 = _init_l_IO_waitAny___auto__1___closed__19();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__19);
l_IO_waitAny___auto__1___closed__20 = _init_l_IO_waitAny___auto__1___closed__20();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__20);
l_IO_waitAny___auto__1___closed__21 = _init_l_IO_waitAny___auto__1___closed__21();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__21);
l_IO_waitAny___auto__1___closed__22 = _init_l_IO_waitAny___auto__1___closed__22();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__22);
l_IO_waitAny___auto__1___closed__23 = _init_l_IO_waitAny___auto__1___closed__23();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__23);
l_IO_waitAny___auto__1___closed__24 = _init_l_IO_waitAny___auto__1___closed__24();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__24);
l_IO_waitAny___auto__1___closed__25 = _init_l_IO_waitAny___auto__1___closed__25();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__25);
l_IO_waitAny___auto__1___closed__26 = _init_l_IO_waitAny___auto__1___closed__26();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__26);
l_IO_waitAny___auto__1___closed__27 = _init_l_IO_waitAny___auto__1___closed__27();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__27);
l_IO_waitAny___auto__1___closed__28 = _init_l_IO_waitAny___auto__1___closed__28();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__28);
l_IO_waitAny___auto__1___closed__29 = _init_l_IO_waitAny___auto__1___closed__29();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__29);
l_IO_waitAny___auto__1___closed__30 = _init_l_IO_waitAny___auto__1___closed__30();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__30);
l_IO_waitAny___auto__1___closed__31 = _init_l_IO_waitAny___auto__1___closed__31();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__31);
l_IO_waitAny___auto__1___closed__32 = _init_l_IO_waitAny___auto__1___closed__32();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__32);
l_IO_waitAny___auto__1___closed__33 = _init_l_IO_waitAny___auto__1___closed__33();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__33);
l_IO_waitAny___auto__1___closed__34 = _init_l_IO_waitAny___auto__1___closed__34();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__34);
l_IO_waitAny___auto__1___closed__35 = _init_l_IO_waitAny___auto__1___closed__35();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__35);
l_IO_waitAny___auto__1___closed__36 = _init_l_IO_waitAny___auto__1___closed__36();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__36);
l_IO_waitAny___auto__1___closed__37 = _init_l_IO_waitAny___auto__1___closed__37();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__37);
l_IO_waitAny___auto__1___closed__38 = _init_l_IO_waitAny___auto__1___closed__38();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__38);
l_IO_waitAny___auto__1___closed__39 = _init_l_IO_waitAny___auto__1___closed__39();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__39);
l_IO_waitAny___auto__1___closed__40 = _init_l_IO_waitAny___auto__1___closed__40();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__40);
l_IO_waitAny___auto__1___closed__41 = _init_l_IO_waitAny___auto__1___closed__41();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__41);
l_IO_waitAny___auto__1___closed__42 = _init_l_IO_waitAny___auto__1___closed__42();
lean_mark_persistent(l_IO_waitAny___auto__1___closed__42);
l_IO_waitAny___auto__1 = _init_l_IO_waitAny___auto__1();
lean_mark_persistent(l_IO_waitAny___auto__1);
l_IO_waitAny_x27___auto__1 = _init_l_IO_waitAny_x27___auto__1();
lean_mark_persistent(l_IO_waitAny_x27___auto__1);
l_IO_waitAny_x27___redArg___closed__0 = _init_l_IO_waitAny_x27___redArg___closed__0();
lean_mark_persistent(l_IO_waitAny_x27___redArg___closed__0);
l_IO_FS_instInhabitedStream_default___lam__0___closed__0 = _init_l_IO_FS_instInhabitedStream_default___lam__0___closed__0();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___lam__0___closed__0);
l_IO_FS_instInhabitedStream_default___lam__0___closed__1 = _init_l_IO_FS_instInhabitedStream_default___lam__0___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___lam__0___closed__1);
l_IO_FS_instInhabitedStream_default___closed__0 = _init_l_IO_FS_instInhabitedStream_default___closed__0();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__0);
l_IO_FS_instInhabitedStream_default___closed__1 = _init_l_IO_FS_instInhabitedStream_default___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__1);
l_IO_FS_instInhabitedStream_default___closed__2 = _init_l_IO_FS_instInhabitedStream_default___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__2);
l_IO_FS_instInhabitedStream_default___closed__3 = _init_l_IO_FS_instInhabitedStream_default___closed__3();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__3);
l_IO_FS_instInhabitedStream_default___closed__4 = _init_l_IO_FS_instInhabitedStream_default___closed__4();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__4);
l_IO_FS_instInhabitedStream_default___closed__5 = _init_l_IO_FS_instInhabitedStream_default___closed__5();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__5);
l_IO_FS_instInhabitedStream_default___closed__6 = _init_l_IO_FS_instInhabitedStream_default___closed__6();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default___closed__6);
l_IO_FS_instInhabitedStream_default = _init_l_IO_FS_instInhabitedStream_default();
lean_mark_persistent(l_IO_FS_instInhabitedStream_default);
l_IO_FS_instInhabitedStream = _init_l_IO_FS_instInhabitedStream();
lean_mark_persistent(l_IO_FS_instInhabitedStream);
l_IO_FS_Handle_readToEnd___closed__0 = _init_l_IO_FS_Handle_readToEnd___closed__0();
lean_mark_persistent(l_IO_FS_Handle_readToEnd___closed__0);
l_IO_FS_Handle_readToEnd___closed__1 = _init_l_IO_FS_Handle_readToEnd___closed__1();
lean_mark_persistent(l_IO_FS_Handle_readToEnd___closed__1);
l_IO_FS_Handle_lines___closed__0 = _init_l_IO_FS_Handle_lines___closed__0();
lean_mark_persistent(l_IO_FS_Handle_lines___closed__0);
l_IO_FS_instReprDirEntry_repr___redArg___closed__0 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__0();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__0);
l_IO_FS_instReprDirEntry_repr___redArg___closed__1 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__1();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__1);
l_IO_FS_instReprDirEntry_repr___redArg___closed__2 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__2();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__2);
l_IO_FS_instReprDirEntry_repr___redArg___closed__3 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__3();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__3);
l_IO_FS_instReprDirEntry_repr___redArg___closed__4 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__4();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__4);
l_IO_FS_instReprDirEntry_repr___redArg___closed__5 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__5();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__5);
l_IO_FS_instReprDirEntry_repr___redArg___closed__6 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__6();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__6);
l_IO_FS_instReprDirEntry_repr___redArg___closed__7 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
l_IO_FS_instReprDirEntry_repr___redArg___closed__8 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__8();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__8);
l_IO_FS_instReprDirEntry_repr___redArg___closed__9 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__9();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__9);
l_IO_FS_instReprDirEntry_repr___redArg___closed__10 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__10();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__10);
l_IO_FS_instReprDirEntry_repr___redArg___closed__11 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__11();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__11);
l_IO_FS_instReprDirEntry_repr___redArg___closed__12 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__12();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__12);
l_IO_FS_instReprDirEntry_repr___redArg___closed__13 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__13();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__13);
l_IO_FS_instReprDirEntry_repr___redArg___closed__14 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
l_IO_FS_instReprDirEntry_repr___redArg___closed__15 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__15();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__15);
l_IO_FS_instReprDirEntry_repr___redArg___closed__16 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
l_IO_FS_instReprDirEntry_repr___redArg___closed__17 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
l_IO_FS_instReprDirEntry_repr___redArg___closed__18 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__18();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__18);
l_IO_FS_instReprDirEntry_repr___redArg___closed__19 = _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__19();
lean_mark_persistent(l_IO_FS_instReprDirEntry_repr___redArg___closed__19);
l_IO_FS_instReprDirEntry___closed__0 = _init_l_IO_FS_instReprDirEntry___closed__0();
lean_mark_persistent(l_IO_FS_instReprDirEntry___closed__0);
l_IO_FS_instReprDirEntry = _init_l_IO_FS_instReprDirEntry();
lean_mark_persistent(l_IO_FS_instReprDirEntry);
l_IO_FS_instReprFileType_repr___closed__0 = _init_l_IO_FS_instReprFileType_repr___closed__0();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__0);
l_IO_FS_instReprFileType_repr___closed__1 = _init_l_IO_FS_instReprFileType_repr___closed__1();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__1);
l_IO_FS_instReprFileType_repr___closed__2 = _init_l_IO_FS_instReprFileType_repr___closed__2();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__2);
l_IO_FS_instReprFileType_repr___closed__3 = _init_l_IO_FS_instReprFileType_repr___closed__3();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__3);
l_IO_FS_instReprFileType_repr___closed__4 = _init_l_IO_FS_instReprFileType_repr___closed__4();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__4);
l_IO_FS_instReprFileType_repr___closed__5 = _init_l_IO_FS_instReprFileType_repr___closed__5();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__5);
l_IO_FS_instReprFileType_repr___closed__6 = _init_l_IO_FS_instReprFileType_repr___closed__6();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__6);
l_IO_FS_instReprFileType_repr___closed__7 = _init_l_IO_FS_instReprFileType_repr___closed__7();
lean_mark_persistent(l_IO_FS_instReprFileType_repr___closed__7);
l_IO_FS_instReprFileType___closed__0 = _init_l_IO_FS_instReprFileType___closed__0();
lean_mark_persistent(l_IO_FS_instReprFileType___closed__0);
l_IO_FS_instReprFileType = _init_l_IO_FS_instReprFileType();
lean_mark_persistent(l_IO_FS_instReprFileType);
l_IO_FS_instBEqFileType___closed__0 = _init_l_IO_FS_instBEqFileType___closed__0();
lean_mark_persistent(l_IO_FS_instBEqFileType___closed__0);
l_IO_FS_instBEqFileType = _init_l_IO_FS_instBEqFileType();
lean_mark_persistent(l_IO_FS_instBEqFileType);
l_IO_FS_instReprSystemTime_repr___redArg___closed__0 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__0();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__0);
l_IO_FS_instReprSystemTime_repr___redArg___closed__1 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__1();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__1);
l_IO_FS_instReprSystemTime_repr___redArg___closed__2 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__2();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__2);
l_IO_FS_instReprSystemTime_repr___redArg___closed__3 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__3();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__3);
l_IO_FS_instReprSystemTime_repr___redArg___closed__4 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
l_IO_FS_instReprSystemTime_repr___redArg___closed__5 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__5();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__5);
l_IO_FS_instReprSystemTime_repr___redArg___closed__6 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__6();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__6);
l_IO_FS_instReprSystemTime_repr___redArg___closed__7 = _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7();
lean_mark_persistent(l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
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
l_IO_FS_instInhabitedSystemTime_default___closed__0 = _init_l_IO_FS_instInhabitedSystemTime_default___closed__0();
l_IO_FS_instInhabitedSystemTime_default___closed__1 = _init_l_IO_FS_instInhabitedSystemTime_default___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime_default___closed__1);
l_IO_FS_instInhabitedSystemTime_default = _init_l_IO_FS_instInhabitedSystemTime_default();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime_default);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
l_IO_FS_instReprMetadata_repr___redArg___closed__0 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__0();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__0);
l_IO_FS_instReprMetadata_repr___redArg___closed__1 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__1();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__1);
l_IO_FS_instReprMetadata_repr___redArg___closed__2 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__2();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__2);
l_IO_FS_instReprMetadata_repr___redArg___closed__3 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__3();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__3);
l_IO_FS_instReprMetadata_repr___redArg___closed__4 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__4();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__4);
l_IO_FS_instReprMetadata_repr___redArg___closed__5 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__5();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__5);
l_IO_FS_instReprMetadata_repr___redArg___closed__6 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__6();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__6);
l_IO_FS_instReprMetadata_repr___redArg___closed__7 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__7();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__7);
l_IO_FS_instReprMetadata_repr___redArg___closed__8 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__8();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__8);
l_IO_FS_instReprMetadata_repr___redArg___closed__9 = _init_l_IO_FS_instReprMetadata_repr___redArg___closed__9();
lean_mark_persistent(l_IO_FS_instReprMetadata_repr___redArg___closed__9);
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
l_IO_withStdin___redArg___closed__0 = _init_l_IO_withStdin___redArg___closed__0();
lean_mark_persistent(l_IO_withStdin___redArg___closed__0);
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
l_IO_Process_output___closed__1 = _init_l_IO_Process_output___closed__1();
lean_mark_persistent(l_IO_Process_output___closed__1);
l_IO_Process_run___closed__0 = _init_l_IO_Process_run___closed__0();
lean_mark_persistent(l_IO_Process_run___closed__0);
l_IO_Process_run___closed__1 = _init_l_IO_Process_run___closed__1();
lean_mark_persistent(l_IO_Process_run___closed__1);
l_IO_Process_run___closed__2 = _init_l_IO_Process_run___closed__2();
lean_mark_persistent(l_IO_Process_run___closed__2);
l_IO_instMonadLiftSTRealWorldBaseIO___closed__0 = _init_l_IO_instMonadLiftSTRealWorldBaseIO___closed__0();
lean_mark_persistent(l_IO_instMonadLiftSTRealWorldBaseIO___closed__0);
l_IO_instMonadLiftSTRealWorldBaseIO = _init_l_IO_instMonadLiftSTRealWorldBaseIO();
lean_mark_persistent(l_IO_instMonadLiftSTRealWorldBaseIO);
l_IO_FS_Stream_ofBuffer___lam__3___closed__0 = _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__0();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___lam__3___closed__0);
l_IO_FS_Stream_ofBuffer___lam__3___closed__1 = _init_l_IO_FS_Stream_ofBuffer___lam__3___closed__1();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___lam__3___closed__1);
l_IO_FS_Stream_ofBuffer___closed__0 = _init_l_IO_FS_Stream_ofBuffer___closed__0();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___closed__0);
l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1 = _init_l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1);
l_IO_FS_Stream_readToEnd___closed__0 = _init_l_IO_FS_Stream_readToEnd___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readToEnd___closed__0);
l_IO_FS_Stream_readToEnd___closed__1 = _init_l_IO_FS_Stream_readToEnd___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readToEnd___closed__1);
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
l_termPrintln_x21_____00__closed__0 = _init_l_termPrintln_x21_____00__closed__0();
lean_mark_persistent(l_termPrintln_x21_____00__closed__0);
l_termPrintln_x21_____00__closed__1 = _init_l_termPrintln_x21_____00__closed__1();
lean_mark_persistent(l_termPrintln_x21_____00__closed__1);
l_termPrintln_x21_____00__closed__2 = _init_l_termPrintln_x21_____00__closed__2();
lean_mark_persistent(l_termPrintln_x21_____00__closed__2);
l_termPrintln_x21_____00__closed__3 = _init_l_termPrintln_x21_____00__closed__3();
lean_mark_persistent(l_termPrintln_x21_____00__closed__3);
l_termPrintln_x21_____00__closed__4 = _init_l_termPrintln_x21_____00__closed__4();
lean_mark_persistent(l_termPrintln_x21_____00__closed__4);
l_termPrintln_x21_____00__closed__5 = _init_l_termPrintln_x21_____00__closed__5();
lean_mark_persistent(l_termPrintln_x21_____00__closed__5);
l_termPrintln_x21_____00__closed__6 = _init_l_termPrintln_x21_____00__closed__6();
lean_mark_persistent(l_termPrintln_x21_____00__closed__6);
l_termPrintln_x21_____00__closed__7 = _init_l_termPrintln_x21_____00__closed__7();
lean_mark_persistent(l_termPrintln_x21_____00__closed__7);
l_termPrintln_x21_____00__closed__8 = _init_l_termPrintln_x21_____00__closed__8();
lean_mark_persistent(l_termPrintln_x21_____00__closed__8);
l_termPrintln_x21_____00__closed__9 = _init_l_termPrintln_x21_____00__closed__9();
lean_mark_persistent(l_termPrintln_x21_____00__closed__9);
l_termPrintln_x21_____00__closed__10 = _init_l_termPrintln_x21_____00__closed__10();
lean_mark_persistent(l_termPrintln_x21_____00__closed__10);
l_termPrintln_x21_____00__closed__11 = _init_l_termPrintln_x21_____00__closed__11();
lean_mark_persistent(l_termPrintln_x21_____00__closed__11);
l_termPrintln_x21_____00__closed__12 = _init_l_termPrintln_x21_____00__closed__12();
lean_mark_persistent(l_termPrintln_x21_____00__closed__12);
l_termPrintln_x21_____00__closed__13 = _init_l_termPrintln_x21_____00__closed__13();
lean_mark_persistent(l_termPrintln_x21_____00__closed__13);
l_termPrintln_x21_____00__closed__14 = _init_l_termPrintln_x21_____00__closed__14();
lean_mark_persistent(l_termPrintln_x21_____00__closed__14);
l_termPrintln_x21_____00__closed__15 = _init_l_termPrintln_x21_____00__closed__15();
lean_mark_persistent(l_termPrintln_x21_____00__closed__15);
l_termPrintln_x21_____00__closed__16 = _init_l_termPrintln_x21_____00__closed__16();
lean_mark_persistent(l_termPrintln_x21_____00__closed__16);
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
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
