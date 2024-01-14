// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.EState Init.Control.Reader Init.Data.String Init.Data.ByteArray Init.System.IOError Init.System.FilePath Init.System.ST Init.Data.ToString.Macro Init.Data.Ord
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
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3;
static lean_object* l_IO_FS_instInhabitedStream___closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3;
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_termPrintln_x21_______closed__9;
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20;
static lean_object* l_IO_FS_instInhabitedSystemTime___closed__1;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_cwd___default;
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_termPrintln_x21____;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12;
static lean_object* l_IO_FS_instInhabitedStream___closed__4;
static lean_object* l_IO_FS_instInhabitedStream___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runEval(lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605_(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8;
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__5;
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2;
lean_object* lean_io_remove_file(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__10;
static uint32_t l_IO_AccessRight_flags___closed__11;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_check_canceled(lean_object*);
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
lean_object* lean_io_has_finished(lean_object*, lean_object*);
static uint32_t l_IO_FS_instInhabitedStream___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___rarg(lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__8;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalUnit(lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17;
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436____boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runEval___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_other___default;
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedSystemTime___closed__2;
LEAN_EXPORT lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168_;
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime;
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18;
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13;
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__1;
static lean_object* l_termPrintln_x21_______closed__1;
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO(lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16;
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9;
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____boxed(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FileRight_user___default___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object*, lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__4;
LEAN_EXPORT lean_object* l_IO_withStderr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16;
lean_object* lean_io_remove_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22;
static uint32_t l_IO_AccessRight_flags___closed__2;
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6;
static lean_object* l_termPrintln_x21_______closed__13;
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
LEAN_EXPORT lean_object* l_Lean_instEval(lean_object*);
static lean_object* l_Lean_instEvalUnit___rarg___closed__2;
static lean_object* l_termPrintln_x21_______closed__3;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime;
LEAN_EXPORT lean_object* l_instInhabitedEIO___rarg(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO;
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__7;
static uint32_t l_IO_AccessRight_flags___closed__12;
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg(uint8_t, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__8;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5;
LEAN_EXPORT lean_object* l___auto____x40_Init_System_IO___hyg_1344_;
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___closed__3;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* l_ByteArray_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*, lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_Buffer_pos___default;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
static lean_object* l_IO_FS_instReprFileType___closed__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11;
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_runEval___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4;
static lean_object* l_termPrintln_x21_______closed__4;
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16;
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
static lean_object* l_IO_Process_output___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7;
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2(size_t, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabitedEStateM___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instBEqSystemTime___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8;
LEAN_EXPORT lean_object* l_EIO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20;
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__1;
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3;
lean_object* lean_io_wait_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7;
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
static lean_object* l_instMonadFinallyEIO___closed__1;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_appDir(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_runEval___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15;
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13;
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Int_repr(lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14;
LEAN_EXPORT uint8_t l_IO_AccessRight_execution___default;
lean_object* lean_get_stdin(lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8;
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__4;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8;
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7;
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1;
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13;
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_env___default;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12;
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17;
LEAN_EXPORT lean_object* l_instMonadBaseIO;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonadExceptOfEStateM___rarg(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20;
static lean_object* l_IO_FS_instReprMetadata___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__6;
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7;
lean_object* lean_task_get_own(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_instEvalUnit___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object*, lean_object*);
static lean_object* l_instMonadEIO___closed__1;
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stdin___default;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289_(uint8_t, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__5;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry;
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_IO_FS_instBEqFileType___closed__1;
static lean_object* l_IO_FS_Mode_noConfusion___rarg___closed__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AccessRight_write___default;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746_(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___closed__1;
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436_(uint8_t, uint8_t);
static lean_object* l_termPrintln_x21_______closed__12;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__12;
LEAN_EXPORT lean_object* l_Lean_runEval___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stderr___default;
LEAN_EXPORT lean_object* l_unsafeBaseIO___rarg(lean_object*);
static lean_object* l_termPrintln_x21_______closed__15;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__13;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__5;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2;
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Process_SpawnArgs_setsid___default;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1;
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6;
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__8;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__1;
LEAN_EXPORT lean_object* l_EIO_catchExceptions___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*);
static lean_object* l_IO_Process_run___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11;
lean_object* l_EStateM_instMonadFinallyEStateM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__16;
LEAN_EXPORT lean_object* l_Lean_instEvalIO(lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__2;
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24;
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_args___default;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
static lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Task_Priority_dedicated;
static lean_object* l_IO_withStdin___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType;
lean_object* lean_io_app_path(lean_object*);
uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__1;
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__10;
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471_(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__6;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
static lean_object* l_termPrintln_x21_______closed__10;
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*);
static lean_object* l_termPrintln_x21_______closed__2;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605____boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
static lean_object* l_IO_FS_instInhabitedStream___lambda__1___closed__2;
lean_object* lean_chmod(lean_object*, uint32_t, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6;
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21;
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*);
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
static lean_object* l_termPrintln_x21_______closed__14;
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_Buffer_data___default;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10;
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2___boxed(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2;
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___rarg(lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14;
LEAN_EXPORT lean_object* l_IO_FileRight_user___default;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
lean_object* lean_io_initializing(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__3;
LEAN_EXPORT lean_object* l_Lean_instEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_termPrintln_x21_______closed__17;
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__14;
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__11;
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO___rarg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
static lean_object* l_IO_FS_instReprDirEntry___closed__1;
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528_(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FileRight_group___default;
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4;
static lean_object* l_IO_FS_instOrdSystemTime___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__2;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__11;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6;
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10;
LEAN_EXPORT lean_object* l_IO_asTask___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13;
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23;
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___rarg(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17;
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
static uint32_t l_IO_AccessRight_flags___closed__7;
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__3;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12;
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5;
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
lean_object* lean_io_process_get_pid(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18;
LEAN_EXPORT lean_object* l_EIO_asTask___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__6;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*);
static lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_runEval___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stdout___default;
LEAN_EXPORT lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AccessRight_read___default;
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9;
lean_object* l_EStateM_nonBacktrackable(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16;
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_object* lean_io_process_child_kill(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
static lean_object* l_termPrintln_x21_______closed__7;
static uint32_t l_IO_AccessRight_flags___closed__9;
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object*);
static lean_object* l___auto____x40_Init_System_IO___hyg_1344____closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4;
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instMonadEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadEIO___closed__1;
return x_2;
}
}
static lean_object* _init_l_instMonadFinallyEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonadFinallyEStateM), 4, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadFinallyEIO___closed__1;
return x_2;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_nonBacktrackable(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadExceptOfEIO___closed__1;
x_2 = l_EStateM_instMonadExceptOfEStateM___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadExceptOfEIO___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabitedEStateM___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instInhabitedEIO___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_instMonadBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMonadFinallyBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadFinallyEIO___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_toEIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_catchExceptions___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BaseIO_toIO___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO_x27___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_toEIO___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeBaseIO___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_unsafeEIO___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeIO___rarg), 1, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_map_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_bind_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_BaseIO_mapTasks_go___rarg(x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_List_reverse___rarg(x_4);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_io_as_task(x_7, x_2, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___rarg___lambda__1), 6, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_io_bind_task(x_9, x_11, x_2, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_BaseIO_mapTasks_go___rarg(x_1, x_3, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_mapTasks___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_asTask___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_io_map_task(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_io_bind_task(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_BaseIO_mapTasks___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_mapTasks___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_ofExcept___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_lazyPure___rarg), 2, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_3 = lean_alloc_closure((void*)(l_IO_sleep___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_dbg_sleep(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_sleep___lambda__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_IO_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_asTask___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_io_map_task(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_mapTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_io_bind_task(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_bindTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_BaseIO_mapTasks___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_mapTasks___rarg), 4, 0);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_has_finished(x_2, x_3);
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
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO", 2);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticNonempty_list", 19);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init", 4);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("System", 6);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11;
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13;
x_2 = lean_unsigned_to_nat(1168u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nonempty_list", 13);
return x_1;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168_() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17;
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exact", 5);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3;
x_4 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6;
x_4 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat.zero_lt_succ", 16);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zero_lt_succ", 12);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6;
x_4 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13;
x_16 = l_Lean_addMacroScope(x_12, x_15, x_11);
x_17 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10;
x_18 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15;
lean_inc(x_10);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20;
lean_inc(x_10);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19;
lean_inc(x_10);
x_23 = l_Lean_Syntax_node1(x_10, x_22, x_21);
x_24 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17;
lean_inc(x_10);
x_25 = l_Lean_Syntax_node1(x_10, x_24, x_23);
x_26 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node2(x_10, x_26, x_19, x_25);
x_28 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5;
x_29 = l_Lean_Syntax_node2(x_10, x_28, x_14, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3;
x_4 = l___auto____x40_Init_System_IO___hyg_1344____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3;
x_4 = l___auto____x40_Init_System_IO___hyg_1344____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14;
x_3 = l___auto____x40_Init_System_IO___hyg_1344____closed__7;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17;
x_3 = l___auto____x40_Init_System_IO___hyg_1344____closed__9;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__5;
x_3 = l___auto____x40_Init_System_IO___hyg_1344____closed__11;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_System_IO___hyg_1344____closed__2;
x_3 = l___auto____x40_Init_System_IO___hyg_1344____closed__13;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_System_IO___hyg_1344_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__14;
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
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Mode_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Mode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_Mode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint32_t _init_l_IO_FS_instInhabitedStream___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lambda__1___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__1;
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_FS_instInhabitedStream___closed__1;
x_2 = l_IO_FS_instInhabitedStream___closed__2;
x_3 = l_IO_FS_instInhabitedStream___closed__3;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedStream___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_instInhabitedStream___lambda__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream___lambda__3(x_1, x_2);
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
LEAN_EXPORT lean_object* l_IO_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_iterate___rarg), 3, 0);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withFile___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_withFile___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
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
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEnd_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_ByteArray_empty;
x_4 = l_IO_FS_Handle_readBinToEnd_loop(x_1, x_3, x_2);
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
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_String_isEmpty(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_4);
x_9 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_String_isEmpty(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_string_append(x_2, x_11);
lean_dec(x_11);
x_2 = x_14;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readToEnd_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_4 = l_IO_FS_Handle_readToEnd_loop(x_1, x_3, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_io_prim_handle_mk(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_ByteArray_empty;
x_8 = l_IO_FS_Handle_readBinToEnd_loop(x_5, x_7, x_6);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_io_prim_handle_mk(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_8 = l_IO_FS_Handle_readToEnd_loop(x_5, x_7, x_6);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_length(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = l_String_back(x_6);
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_2, x_6);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_String_dropRight(x_6, x_15);
x_17 = l_System_Platform_isWindows;
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_push(x_2, x_16);
x_2 = x_18;
x_3 = x_7;
goto _start;
}
else
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = l_String_back(x_16);
x_21 = 13;
x_22 = lean_uint32_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_array_push(x_2, x_16);
x_2 = x_23;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_String_dropRight(x_16, x_15);
x_26 = lean_array_push(x_2, x_25);
x_2 = x_26;
x_3 = x_7;
goto _start;
}
}
}
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_string_length(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
uint32_t x_33; uint32_t x_34; uint8_t x_35; 
x_33 = l_String_back(x_28);
x_34 = 10;
x_35 = lean_uint32_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_push(x_2, x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_String_dropRight(x_28, x_38);
x_40 = l_System_Platform_isWindows;
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_array_push(x_2, x_39);
x_2 = x_41;
x_3 = x_29;
goto _start;
}
else
{
uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_43 = l_String_back(x_39);
x_44 = 13;
x_45 = lean_uint32_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_array_push(x_2, x_39);
x_2 = x_46;
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_String_dropRight(x_39, x_38);
x_49 = lean_array_push(x_2, x_48);
x_2 = x_49;
x_3 = x_29;
goto _start;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_28);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
return x_4;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_io_prim_handle_mk(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
x_8 = l_IO_FS_lines_read(x_5, x_7, x_6);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_prim_handle_write(x_6, x_2, x_7);
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_9; 
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
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_prim_handle_put_str(x_6, x_2, x_7);
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_9; 
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
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("root", 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FilePath.mk ", 12);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fileName", 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" }", 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_String_quote(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Repr_addAppParen(x_7, x_8);
x_10 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_1, 1);
x_25 = l_String_quote(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_12);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_12);
return x_37;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprDirEntry___closed__1;
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
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_FileType_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_FileType_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.FS.FileType.dir", 18);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.FS.FileType.file", 19);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.FS.FileType.symlink", 22);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.FS.FileType.other", 20);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
case 2:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
default: 
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instReprFileType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprFileType___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqFileType___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sec", 3);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nsec", 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Int_repr(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_21 = lean_uint32_to_nat(x_20);
x_22 = l_Nat_repr(x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_8);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_8);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprSystemTime___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528_(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_uint32_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2528____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqSystemTime___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2605____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instOrdSystemTime___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__1;
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__2;
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
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("accessed", 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("modified", 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("byteSize", 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type", 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471_(x_3, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
x_21 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471_(x_20, x_4);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_8);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_31 = lean_uint64_to_nat(x_30);
x_32 = l_Nat_repr(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_8);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_14);
x_39 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_18);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_43 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289_(x_42, x_4);
x_44 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7;
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_8);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_8);
return x_54;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprMetadata___closed__1;
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
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 8);
lean_dec(x_5);
x_7 = 0;
x_8 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436_(x_6, x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*2 + 8);
lean_dec(x_10);
x_13 = 0;
x_14 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2436_(x_12, x_13);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = 1;
x_7 = lean_box(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_134; lean_object* x_135; 
lean_dec(x_6);
x_21 = lean_array_uget(x_3, x_5);
x_22 = l_IO_FS_DirEntry_path(x_21);
lean_inc(x_22);
x_134 = lean_array_push(x_7, x_22);
x_135 = lean_io_metadata(x_22, x_8);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
x_23 = x_139;
x_24 = x_137;
goto block_133;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_dec(x_135);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_134);
x_23 = x_143;
x_24 = x_141;
goto block_133;
}
block_133:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 11)
{
uint8_t x_27; 
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_23, 0, x_29);
x_9 = x_23;
x_10 = x_24;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_9 = x_32;
x_10 = x_24;
goto block_17;
}
}
else
{
lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*2 + 8);
lean_dec(x_34);
x_36 = lean_box(x_35);
switch (lean_obj_tag(x_36)) {
case 0:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
lean_inc(x_1);
x_38 = l_System_FilePath_walkDir_go(x_1, x_22, x_37, x_24);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_39, 0, x_43);
x_9 = x_39;
x_10 = x_40;
goto block_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_9 = x_46;
x_10 = x_40;
goto block_17;
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 2:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 1);
x_53 = lean_ctor_get(x_23, 0);
lean_dec(x_53);
x_54 = lean_io_realpath(x_22, x_24);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_System_FilePath_isDir(x_55, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_23, 0, x_61);
x_9 = x_23;
x_10 = x_60;
goto block_17;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
lean_inc(x_1);
lean_inc(x_2);
x_63 = lean_apply_2(x_1, x_2, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_23, 0, x_67);
x_9 = x_23;
x_10 = x_66;
goto block_17;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_free_object(x_23);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
lean_inc(x_1);
x_69 = l_System_FilePath_walkDir_go(x_1, x_55, x_52, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
x_74 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_70, 0, x_74);
x_9 = x_70;
x_10 = x_71;
goto block_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_9 = x_77;
x_10 = x_71;
goto block_17;
}
}
else
{
uint8_t x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
return x_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_69, 0);
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_69);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_55);
lean_free_object(x_23);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_63);
if (x_82 == 0)
{
return x_63;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_63, 0);
x_84 = lean_ctor_get(x_63, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_63);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_23);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_54);
if (x_86 == 0)
{
return x_54;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_54, 0);
x_88 = lean_ctor_get(x_54, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_54);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_23, 1);
lean_inc(x_90);
lean_dec(x_23);
x_91 = lean_io_realpath(x_22, x_24);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_System_FilePath_isDir(x_92, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_92);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_90);
x_9 = x_99;
x_10 = x_97;
goto block_17;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
lean_inc(x_1);
lean_inc(x_2);
x_101 = lean_apply_2(x_1, x_2, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_92);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_90);
x_9 = x_106;
x_10 = x_104;
goto block_17;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
lean_inc(x_1);
x_108 = l_System_FilePath_walkDir_go(x_1, x_92, x_90, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
x_9 = x_114;
x_10 = x_110;
goto block_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_101, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_121 = x_101;
} else {
 lean_dec_ref(x_101);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_90);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_91, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_91, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_125 = x_91;
} else {
 lean_dec_ref(x_91);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
default: 
{
uint8_t x_127; 
lean_dec(x_36);
lean_dec(x_22);
x_127 = !lean_is_exclusive(x_23);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_23, 0);
lean_dec(x_128);
x_129 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_23, 0, x_129);
x_9 = x_23;
x_10 = x_24;
goto block_17;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_23, 1);
lean_inc(x_130);
lean_dec(x_23);
x_131 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_9 = x_132;
x_10 = x_24;
goto block_17;
}
}
}
}
}
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_13;
x_7 = x_12;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_read_dir(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(x_2, x_1, x_7, x_10, x_11, x_12, x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_13;
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
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = l_System_FilePath_walkDir_go___lambda__1(x_2, x_1, x_17, x_3, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_System_FilePath_walkDir_go___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
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
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_IO_withStdin___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__3), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStdin___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_withStdin___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_withStdin___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStdout___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStdout___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStderr___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStderr___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_print___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_IO_print(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_print___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_print___at_IO_println___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
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
LEAN_EXPORT lean_object* l_IO_println___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_print___at_IO_println___spec__1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_println___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprint___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_eprintln___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_eprint___at_IO_eprintln___spec__1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprintln___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at_IO_eprintln___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at_IO_eprintln___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_appDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("System.IO.appDir: unexpected filename '", 39);
return x_1;
}
}
static lean_object* _init_l_IO_appDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
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
x_7 = l_IO_appDir___closed__1;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = l_IO_appDir___closed__2;
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
x_17 = l_IO_appDir___closed__1;
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_IO_appDir___closed__2;
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
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_IO_FS_createDirAll___lambda__1(x_1, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_IO_FS_createDirAll(x_7, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_FS_createDirAll___lambda__1(x_1, x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = l_IO_FS_createDirAll___lambda__2(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_createDirAll___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_createDirAll___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = l_IO_FS_DirEntry_path(x_8);
x_10 = l_System_FilePath_isDir(x_9, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_io_remove_file(x_9, x_13);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_box(0);
x_3 = x_17;
x_4 = x_18;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_IO_FS_removeDirAll(x_9, x_24);
lean_dec(x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_box(0);
x_3 = x_28;
x_4 = x_29;
x_5 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_box(0);
x_10 = l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(x_4, x_7, x_8, x_9, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_io_remove_dir(x_1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Process_Stdio_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_Process_Stdio_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stdin___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stdout___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stderr___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_args___default() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_cwd___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_env___default() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_System_IO___hyg_1344____closed__3;
return x_1;
}
}
static uint8_t _init_l_IO_Process_SpawnArgs_setsid___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
static lean_object* _init_l_IO_Process_output___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
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
x_5 = l_IO_Process_output___closed__1;
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Task_Priority_dedicated;
x_13 = lean_io_as_task(x_11, x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
x_17 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_18 = l_IO_FS_Handle_readToEnd_loop(x_16, x_17, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_5, x_7, x_20);
lean_dec(x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_task_get_own(x_14);
x_25 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint32_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_29 = lean_unbox_uint32(x_22);
lean_dec(x_22);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_29);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_19);
x_33 = lean_unbox_uint32(x_22);
lean_dec(x_22);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_14);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
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
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_14);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
return x_6;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
x_54 = lean_ctor_get(x_1, 4);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_56 = l_IO_Process_output___closed__1;
x_57 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*5, x_55);
x_58 = lean_io_process_spawn(x_57, x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = l_Task_Priority_dedicated;
x_65 = lean_io_as_task(x_63, x_64, x_60);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_59, 2);
lean_inc(x_68);
x_69 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_70 = l_IO_FS_Handle_readToEnd_loop(x_68, x_69, x_67);
lean_dec(x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_io_process_child_wait(x_56, x_59, x_72);
lean_dec(x_59);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_task_get_own(x_66);
x_77 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_76, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint32_t x_82; lean_object* x_83; 
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
x_81 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_71);
x_82 = lean_unbox_uint32(x_74);
lean_dec(x_74);
lean_ctor_set_uint32(x_81, sizeof(void*)*2, x_82);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_74);
lean_dec(x_71);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_71);
lean_dec(x_66);
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_66);
lean_dec(x_59);
x_92 = lean_ctor_get(x_70, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_70, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_94 = x_70;
} else {
 lean_dec_ref(x_70);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_58, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_58, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_98 = x_58;
} else {
 lean_dec_ref(x_58);
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
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_IO_Process_run___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("process '", 9);
return x_1;
}
}
static lean_object* _init_l_IO_Process_run___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' exited with code ", 19);
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
lean_object* x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_8 = 0;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_IO_Process_run___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_IO_Process_run___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_uint32_to_nat(x_7);
x_16 = l_Nat_repr(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_IO_Process_run___lambda__1(x_5, x_19, x_6);
lean_dec(x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get_uint32(x_21, sizeof(void*)*2);
x_24 = 0;
x_25 = lean_uint32_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_IO_Process_run___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_IO_Process_run___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_uint32_to_nat(x_23);
x_32 = l_Nat_repr(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = l_IO_Process_run___lambda__1(x_21, x_36, x_22);
lean_dec(x_21);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Process_run___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
static uint8_t _init_l_IO_AccessRight_read___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_IO_AccessRight_write___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_IO_AccessRight_execution___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__1() {
_start:
{
uint32_t x_1; uint32_t x_2; 
x_1 = 0;
x_2 = lean_uint32_lor(x_1, x_1);
return x_2;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__2() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__3() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__4() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__5() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_uint32_lor(x_2, x_1);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__6() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__5;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__7() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__8() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__9() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__10() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__11() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__12() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__11;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__13() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 2);
if (x_4 == 0)
{
uint32_t x_5; 
x_5 = l_IO_AccessRight_flags___closed__2;
return x_5;
}
else
{
uint32_t x_6; 
x_6 = l_IO_AccessRight_flags___closed__4;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, 2);
if (x_7 == 0)
{
uint32_t x_8; 
x_8 = l_IO_AccessRight_flags___closed__6;
return x_8;
}
else
{
uint32_t x_9; 
x_9 = l_IO_AccessRight_flags___closed__8;
return x_9;
}
}
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, 1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, 2);
if (x_11 == 0)
{
uint32_t x_12; 
x_12 = l_IO_AccessRight_flags___closed__9;
return x_12;
}
else
{
uint32_t x_13; 
x_13 = l_IO_AccessRight_flags___closed__10;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, 2);
if (x_14 == 0)
{
uint32_t x_15; 
x_15 = l_IO_AccessRight_flags___closed__12;
return x_15;
}
else
{
uint32_t x_16; 
x_16 = l_IO_AccessRight_flags___closed__13;
return x_16;
}
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
static lean_object* _init_l_IO_FileRight_user___default___closed__1() {
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
static lean_object* _init_l_IO_FileRight_user___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FileRight_group___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FileRight_other___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_IO_AccessRight_flags(x_2);
x_4 = 6;
x_5 = lean_uint32_shift_left(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_IO_AccessRight_flags(x_6);
x_8 = 3;
x_9 = lean_uint32_shift_left(x_7, x_8);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_IO_AccessRight_flags(x_10);
x_12 = lean_uint32_lor(x_9, x_11);
x_13 = lean_uint32_lor(x_5, x_12);
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
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_read(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__5___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__4___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__3___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__2___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofHandle___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_Buffer_data___default() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_Buffer_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_string_to_utf8(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_byte_array_size(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_byte_array_copy_slice(x_7, x_11, x_8, x_9, x_10, x_12);
lean_dec(x_7);
x_14 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_st_ref_set(x_1, x_15, x_6);
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
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_byte_array_get(x_1, x_2);
x_7 = 0;
x_8 = lean_uint8_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = 10;
x_10 = lean_uint8_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_byte_array_size(x_7);
x_11 = l_ByteArray_extract(x_7, x_8, x_10);
x_12 = lean_string_from_utf8_unchecked(x_11);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_10);
x_13 = lean_st_ref_set(x_1, x_4, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_byte_array_get(x_7, x_18);
x_20 = 0;
x_21 = lean_uint8_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
x_24 = l_ByteArray_extract(x_7, x_8, x_23);
x_25 = lean_string_from_utf8_unchecked(x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_23);
x_26 = lean_st_ref_set(x_1, x_4, x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_ByteArray_extract(x_7, x_8, x_18);
x_32 = lean_string_from_utf8_unchecked(x_31);
lean_dec(x_31);
lean_ctor_set(x_4, 1, x_18);
x_33 = lean_st_ref_set(x_1, x_4, x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
lean_inc(x_39);
x_40 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_byte_array_size(x_38);
x_42 = l_ByteArray_extract(x_38, x_39, x_41);
x_43 = lean_string_from_utf8_unchecked(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_st_ref_set(x_1, x_44, x_5);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_byte_array_get(x_38, x_49);
x_51 = 0;
x_52 = lean_uint8_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_49, x_53);
lean_dec(x_49);
x_55 = l_ByteArray_extract(x_38, x_39, x_54);
x_56 = lean_string_from_utf8_unchecked(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_st_ref_set(x_1, x_57, x_5);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = l_ByteArray_extract(x_38, x_39, x_49);
x_63 = lean_string_from_utf8_unchecked(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_st_ref_set(x_1, x_64, x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_byte_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
x_12 = lean_byte_array_copy_slice(x_2, x_10, x_7, x_8, x_9, x_11);
x_13 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_ofBuffer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__5), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__4___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__3___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_IO_FS_Stream_ofBuffer___closed__1;
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofBuffer___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_string_from_utf8_unchecked(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_IO_FS_Stream_ofBuffer(x_1);
lean_inc(x_8);
x_10 = l_IO_FS_Stream_ofBuffer(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__2), 5, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
if (x_5 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_3);
x_12 = l_IO_withStdout___rarg(x_3, x_6, x_2, x_10, x_7);
x_13 = l_IO_withStdin___rarg(x_3, x_6, x_2, x_9, x_12);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_3);
x_15 = l_IO_withStderr___rarg(x_3, x_6, x_2, x_10, x_7);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_3);
x_16 = l_IO_withStdout___rarg(x_3, x_6, x_2, x_10, x_15);
x_17 = l_IO_withStdin___rarg(x_3, x_6, x_2, x_9, x_16);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_4);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__3___boxed), 8, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_withIsolatedStreams___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_IO_FS_withIsolatedStreams___rarg___closed__2;
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_box(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__4___boxed), 8, 7);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_2);
lean_closure_set(x_10, 5, x_4);
lean_closure_set(x_10, 6, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_withIsolatedStreams___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_IO_FS_withIsolatedStreams___rarg___lambda__3(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_IO_FS_withIsolatedStreams___rarg___lambda__4(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_IO_FS_withIsolatedStreams___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_IO_println___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = l_IO_println___at_Lean_instEval___spec__1(x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEval___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_1, x_3);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_print___at_IO_println___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = l_IO_println___at_Lean_instEval__1___spec__1(x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEval__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEval__1___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_instEvalUnit___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("()", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_instEvalUnit___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instEvalUnit___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instEvalUnit___rarg___closed__2;
x_4 = l_IO_println___at_Lean_instEval__1___spec__1(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEvalUnit___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_instEvalUnit___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instEvalUnit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_2(x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_apply_3(x_1, x_9, x_11, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEvalIO___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEvalIO___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = lean_apply_2(x_2, x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_apply_3(x_1, x_9, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEvalBaseIO___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalBaseIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEvalBaseIO___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_runEval___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdout(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdout(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_runEval___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdin(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdin(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_runEval___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stderr(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stderr(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stderr(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_IO_FS_withIsolatedStreams___rarg___closed__1;
x_5 = lean_st_mk_ref(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_mk_ref(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_6);
lean_inc(x_9);
x_12 = l_IO_FS_Stream_ofBuffer(x_9);
if (x_2 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_runEval___spec__2), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
x_14 = l_IO_withStdin___at_Lean_runEval___spec__3(x_11, x_13, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_16);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_string_from_utf8_unchecked(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_string_from_utf8_unchecked(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_12);
x_33 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_runEval___spec__4), 3, 2);
lean_closure_set(x_33, 0, x_12);
lean_closure_set(x_33, 1, x_1);
x_34 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_runEval___spec__2), 3, 2);
lean_closure_set(x_34, 0, x_12);
lean_closure_set(x_34, 1, x_33);
x_35 = l_IO_withStdin___at_Lean_runEval___spec__3(x_11, x_34, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_9, x_37);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_string_from_utf8_unchecked(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_string_from_utf8_unchecked(x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_36);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_runEval___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box(x_4);
x_6 = lean_apply_3(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_runEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_runEval___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = 1;
x_6 = l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_runEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_runEval___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termPrintln!__", 14);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("println! ", 9);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("orelse", 6);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStr", 15);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_______closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_______closed__10;
x_2 = l_termPrintln_x21_______closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__8;
x_2 = l_termPrintln_x21_______closed__14;
x_3 = l_termPrintln_x21_______closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__4;
x_2 = l_termPrintln_x21_______closed__6;
x_3 = l_termPrintln_x21_______closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_termPrintln_x21_______closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21____() {
_start:
{
lean_object* x_1; 
x_1 = l_termPrintln_x21_______closed__17;
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStrKind", 19);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscription", 14);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6;
x_4 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.println", 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("println", 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1;
x_2 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2;
x_3 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6;
x_4 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termS!_", 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("s!", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_termPrintln_x21_______closed__2;
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
x_10 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
lean_inc(x_14);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_15);
lean_inc(x_16);
x_20 = l_Lean_addMacroScope(x_16, x_19, x_15);
x_21 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_22 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
lean_inc(x_14);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17;
lean_inc(x_14);
x_25 = l_Lean_Syntax_node1(x_14, x_24, x_9);
x_26 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8;
lean_inc(x_14);
x_27 = l_Lean_Syntax_node2(x_14, x_26, x_23, x_25);
x_28 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
lean_inc(x_14);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
lean_inc(x_15);
lean_inc(x_16);
x_31 = l_Lean_addMacroScope(x_16, x_30, x_15);
x_32 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
x_33 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
lean_inc(x_14);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_33);
x_35 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
x_36 = l_Lean_addMacroScope(x_16, x_35, x_15);
x_37 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_38 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_inc(x_14);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_38);
lean_inc(x_14);
x_40 = l_Lean_Syntax_node1(x_14, x_24, x_39);
lean_inc(x_14);
x_41 = l_Lean_Syntax_node2(x_14, x_26, x_34, x_40);
lean_inc(x_14);
x_42 = l_Lean_Syntax_node1(x_14, x_24, x_41);
x_43 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_14);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
x_46 = l_Lean_Syntax_node5(x_14, x_45, x_18, x_27, x_29, x_42, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
x_49 = 0;
x_50 = l_Lean_SourceInfo_fromRef(x_48, x_49);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_53 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
lean_inc(x_50);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_51);
lean_inc(x_52);
x_56 = l_Lean_addMacroScope(x_52, x_55, x_51);
x_57 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_58 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
lean_inc(x_50);
x_59 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
lean_inc(x_50);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_50);
x_63 = l_Lean_Syntax_node2(x_50, x_62, x_61, x_9);
x_64 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_50);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
lean_inc(x_65);
lean_inc(x_54);
lean_inc(x_50);
x_67 = l_Lean_Syntax_node3(x_50, x_66, x_54, x_63, x_65);
x_68 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17;
lean_inc(x_50);
x_69 = l_Lean_Syntax_node1(x_50, x_68, x_67);
x_70 = l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8;
lean_inc(x_50);
x_71 = l_Lean_Syntax_node2(x_50, x_70, x_59, x_69);
x_72 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
lean_inc(x_50);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_50);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2;
lean_inc(x_51);
lean_inc(x_52);
x_75 = l_Lean_addMacroScope(x_52, x_74, x_51);
x_76 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
x_77 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
lean_inc(x_50);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_50);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_77);
x_79 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
x_80 = l_Lean_addMacroScope(x_52, x_79, x_51);
x_81 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_82 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_inc(x_50);
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_inc(x_50);
x_84 = l_Lean_Syntax_node1(x_50, x_68, x_83);
lean_inc(x_50);
x_85 = l_Lean_Syntax_node2(x_50, x_70, x_78, x_84);
lean_inc(x_50);
x_86 = l_Lean_Syntax_node1(x_50, x_68, x_85);
x_87 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
x_88 = l_Lean_Syntax_node5(x_50, x_87, x_54, x_71, x_73, x_86, x_65);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
lean_object* initialize_Init_Control_EState(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Reader(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IOError(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_ST(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_EState(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instMonadEIO___closed__1 = _init_l_instMonadEIO___closed__1();
lean_mark_persistent(l_instMonadEIO___closed__1);
l_instMonadFinallyEIO___closed__1 = _init_l_instMonadFinallyEIO___closed__1();
lean_mark_persistent(l_instMonadFinallyEIO___closed__1);
l_instMonadExceptOfEIO___closed__1 = _init_l_instMonadExceptOfEIO___closed__1();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__1);
l_instMonadExceptOfEIO___closed__2 = _init_l_instMonadExceptOfEIO___closed__2();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__2);
l_instMonadBaseIO = _init_l_instMonadBaseIO();
lean_mark_persistent(l_instMonadBaseIO);
l_instMonadFinallyBaseIO = _init_l_instMonadFinallyBaseIO();
lean_mark_persistent(l_instMonadFinallyBaseIO);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__1);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__2);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__3);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__4);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__5);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__6);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__7);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__8);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__9);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__10);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__11);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__12);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__13);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__14);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__15);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__16);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17 = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168____closed__17);
l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168_ = _init_l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168_();
lean_mark_persistent(l_IO_tacticNonempty__list____x40_Init_System_IO___hyg_1168_);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__1);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__2);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__3);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__4);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__5);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__6);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__7);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__8);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__9);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__10);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__11);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__12);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__13);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__14);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__15);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__16);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__17);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__18);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__19);
l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20 = _init_l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20();
lean_mark_persistent(l_IO___aux__Init__System__IO______macroRules__IO__tacticNonempty__list__1___closed__20);
l___auto____x40_Init_System_IO___hyg_1344____closed__1 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__1();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__1);
l___auto____x40_Init_System_IO___hyg_1344____closed__2 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__2();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__2);
l___auto____x40_Init_System_IO___hyg_1344____closed__3 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__3();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__3);
l___auto____x40_Init_System_IO___hyg_1344____closed__4 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__4();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__4);
l___auto____x40_Init_System_IO___hyg_1344____closed__5 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__5();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__5);
l___auto____x40_Init_System_IO___hyg_1344____closed__6 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__6();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__6);
l___auto____x40_Init_System_IO___hyg_1344____closed__7 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__7();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__7);
l___auto____x40_Init_System_IO___hyg_1344____closed__8 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__8();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__8);
l___auto____x40_Init_System_IO___hyg_1344____closed__9 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__9();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__9);
l___auto____x40_Init_System_IO___hyg_1344____closed__10 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__10();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__10);
l___auto____x40_Init_System_IO___hyg_1344____closed__11 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__11();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__11);
l___auto____x40_Init_System_IO___hyg_1344____closed__12 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__12();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__12);
l___auto____x40_Init_System_IO___hyg_1344____closed__13 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__13();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__13);
l___auto____x40_Init_System_IO___hyg_1344____closed__14 = _init_l___auto____x40_Init_System_IO___hyg_1344____closed__14();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344____closed__14);
l___auto____x40_Init_System_IO___hyg_1344_ = _init_l___auto____x40_Init_System_IO___hyg_1344_();
lean_mark_persistent(l___auto____x40_Init_System_IO___hyg_1344_);
l_IO_FS_Mode_noConfusion___rarg___closed__1 = _init_l_IO_FS_Mode_noConfusion___rarg___closed__1();
lean_mark_persistent(l_IO_FS_Mode_noConfusion___rarg___closed__1);
l_IO_FS_instInhabitedStream___lambda__1___closed__1 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__1();
l_IO_FS_instInhabitedStream___lambda__1___closed__2 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lambda__1___closed__2);
l_IO_FS_instInhabitedStream___lambda__1___closed__3 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__3();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lambda__1___closed__3);
l_IO_FS_instInhabitedStream___closed__1 = _init_l_IO_FS_instInhabitedStream___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__1);
l_IO_FS_instInhabitedStream___closed__2 = _init_l_IO_FS_instInhabitedStream___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__2);
l_IO_FS_instInhabitedStream___closed__3 = _init_l_IO_FS_instInhabitedStream___closed__3();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__3);
l_IO_FS_instInhabitedStream___closed__4 = _init_l_IO_FS_instInhabitedStream___closed__4();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__4);
l_IO_FS_instInhabitedStream = _init_l_IO_FS_instInhabitedStream();
lean_mark_persistent(l_IO_FS_instInhabitedStream);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__1);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__2);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__3);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__4);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__5);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__6);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__7);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__8);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__9);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__10);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__11);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__12);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__13);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__14);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__15);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__16);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__17);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__18);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__19);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_2216____closed__20);
l_IO_FS_instReprDirEntry___closed__1 = _init_l_IO_FS_instReprDirEntry___closed__1();
lean_mark_persistent(l_IO_FS_instReprDirEntry___closed__1);
l_IO_FS_instReprDirEntry = _init_l_IO_FS_instReprDirEntry();
lean_mark_persistent(l_IO_FS_instReprDirEntry);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__1);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__2);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__3);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__4);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__5);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__6);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__7);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__8);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__9);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__10);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__11);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__12);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__13);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__14);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__15);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__16);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__17);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__18);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__19);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__20);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__21);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__22);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__23);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__24);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__25);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_2289____closed__26);
l_IO_FS_instReprFileType___closed__1 = _init_l_IO_FS_instReprFileType___closed__1();
lean_mark_persistent(l_IO_FS_instReprFileType___closed__1);
l_IO_FS_instReprFileType = _init_l_IO_FS_instReprFileType();
lean_mark_persistent(l_IO_FS_instReprFileType);
l_IO_FS_instBEqFileType___closed__1 = _init_l_IO_FS_instBEqFileType___closed__1();
lean_mark_persistent(l_IO_FS_instBEqFileType___closed__1);
l_IO_FS_instBEqFileType = _init_l_IO_FS_instBEqFileType();
lean_mark_persistent(l_IO_FS_instBEqFileType);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__1);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__2);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__3);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__4);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__5);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__6);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2471____closed__7);
l_IO_FS_instReprSystemTime___closed__1 = _init_l_IO_FS_instReprSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instReprSystemTime___closed__1);
l_IO_FS_instReprSystemTime = _init_l_IO_FS_instReprSystemTime();
lean_mark_persistent(l_IO_FS_instReprSystemTime);
l_IO_FS_instBEqSystemTime___closed__1 = _init_l_IO_FS_instBEqSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instBEqSystemTime___closed__1);
l_IO_FS_instBEqSystemTime = _init_l_IO_FS_instBEqSystemTime();
lean_mark_persistent(l_IO_FS_instBEqSystemTime);
l_IO_FS_instOrdSystemTime___closed__1 = _init_l_IO_FS_instOrdSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instOrdSystemTime___closed__1);
l_IO_FS_instOrdSystemTime = _init_l_IO_FS_instOrdSystemTime();
lean_mark_persistent(l_IO_FS_instOrdSystemTime);
l_IO_FS_instInhabitedSystemTime___closed__1 = _init_l_IO_FS_instInhabitedSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime___closed__1);
l_IO_FS_instInhabitedSystemTime___closed__2 = _init_l_IO_FS_instInhabitedSystemTime___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime___closed__2);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__1);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__2);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__3);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__4);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__5);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__6);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__7);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__8);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__9);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2746____closed__10);
l_IO_FS_instReprMetadata___closed__1 = _init_l_IO_FS_instReprMetadata___closed__1();
lean_mark_persistent(l_IO_FS_instReprMetadata___closed__1);
l_IO_FS_instReprMetadata = _init_l_IO_FS_instReprMetadata();
lean_mark_persistent(l_IO_FS_instReprMetadata);
l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1);
l_IO_withStdin___rarg___lambda__3___closed__1 = _init_l_IO_withStdin___rarg___lambda__3___closed__1();
lean_mark_persistent(l_IO_withStdin___rarg___lambda__3___closed__1);
l_IO_appDir___closed__1 = _init_l_IO_appDir___closed__1();
lean_mark_persistent(l_IO_appDir___closed__1);
l_IO_appDir___closed__2 = _init_l_IO_appDir___closed__2();
lean_mark_persistent(l_IO_appDir___closed__2);
l_IO_Process_StdioConfig_stdin___default = _init_l_IO_Process_StdioConfig_stdin___default();
l_IO_Process_StdioConfig_stdout___default = _init_l_IO_Process_StdioConfig_stdout___default();
l_IO_Process_StdioConfig_stderr___default = _init_l_IO_Process_StdioConfig_stderr___default();
l_IO_Process_SpawnArgs_args___default = _init_l_IO_Process_SpawnArgs_args___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_args___default);
l_IO_Process_SpawnArgs_cwd___default = _init_l_IO_Process_SpawnArgs_cwd___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_cwd___default);
l_IO_Process_SpawnArgs_env___default = _init_l_IO_Process_SpawnArgs_env___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_env___default);
l_IO_Process_SpawnArgs_setsid___default = _init_l_IO_Process_SpawnArgs_setsid___default();
l_IO_Process_output___closed__1 = _init_l_IO_Process_output___closed__1();
lean_mark_persistent(l_IO_Process_output___closed__1);
l_IO_Process_run___closed__1 = _init_l_IO_Process_run___closed__1();
lean_mark_persistent(l_IO_Process_run___closed__1);
l_IO_Process_run___closed__2 = _init_l_IO_Process_run___closed__2();
lean_mark_persistent(l_IO_Process_run___closed__2);
l_IO_AccessRight_read___default = _init_l_IO_AccessRight_read___default();
l_IO_AccessRight_write___default = _init_l_IO_AccessRight_write___default();
l_IO_AccessRight_execution___default = _init_l_IO_AccessRight_execution___default();
l_IO_AccessRight_flags___closed__1 = _init_l_IO_AccessRight_flags___closed__1();
l_IO_AccessRight_flags___closed__2 = _init_l_IO_AccessRight_flags___closed__2();
l_IO_AccessRight_flags___closed__3 = _init_l_IO_AccessRight_flags___closed__3();
l_IO_AccessRight_flags___closed__4 = _init_l_IO_AccessRight_flags___closed__4();
l_IO_AccessRight_flags___closed__5 = _init_l_IO_AccessRight_flags___closed__5();
l_IO_AccessRight_flags___closed__6 = _init_l_IO_AccessRight_flags___closed__6();
l_IO_AccessRight_flags___closed__7 = _init_l_IO_AccessRight_flags___closed__7();
l_IO_AccessRight_flags___closed__8 = _init_l_IO_AccessRight_flags___closed__8();
l_IO_AccessRight_flags___closed__9 = _init_l_IO_AccessRight_flags___closed__9();
l_IO_AccessRight_flags___closed__10 = _init_l_IO_AccessRight_flags___closed__10();
l_IO_AccessRight_flags___closed__11 = _init_l_IO_AccessRight_flags___closed__11();
l_IO_AccessRight_flags___closed__12 = _init_l_IO_AccessRight_flags___closed__12();
l_IO_AccessRight_flags___closed__13 = _init_l_IO_AccessRight_flags___closed__13();
l_IO_FileRight_user___default___closed__1 = _init_l_IO_FileRight_user___default___closed__1();
lean_mark_persistent(l_IO_FileRight_user___default___closed__1);
l_IO_FileRight_user___default = _init_l_IO_FileRight_user___default();
lean_mark_persistent(l_IO_FileRight_user___default);
l_IO_FileRight_group___default = _init_l_IO_FileRight_group___default();
lean_mark_persistent(l_IO_FileRight_group___default);
l_IO_FileRight_other___default = _init_l_IO_FileRight_other___default();
lean_mark_persistent(l_IO_FileRight_other___default);
l_IO_FS_Stream_Buffer_data___default = _init_l_IO_FS_Stream_Buffer_data___default();
lean_mark_persistent(l_IO_FS_Stream_Buffer_data___default);
l_IO_FS_Stream_Buffer_pos___default = _init_l_IO_FS_Stream_Buffer_pos___default();
lean_mark_persistent(l_IO_FS_Stream_Buffer_pos___default);
l_IO_FS_Stream_ofBuffer___closed__1 = _init_l_IO_FS_Stream_ofBuffer___closed__1();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__2);
l_Lean_instEvalUnit___rarg___closed__1 = _init_l_Lean_instEvalUnit___rarg___closed__1();
lean_mark_persistent(l_Lean_instEvalUnit___rarg___closed__1);
l_Lean_instEvalUnit___rarg___closed__2 = _init_l_Lean_instEvalUnit___rarg___closed__2();
lean_mark_persistent(l_Lean_instEvalUnit___rarg___closed__2);
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
l_termPrintln_x21_______closed__17 = _init_l_termPrintln_x21_______closed__17();
lean_mark_persistent(l_termPrintln_x21_______closed__17);
l_termPrintln_x21____ = _init_l_termPrintln_x21____();
lean_mark_persistent(l_termPrintln_x21____);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
