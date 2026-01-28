// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: public import Lean.Server.Utils public import Lean.Util.LakePath public import Lean.Server.ServerTask
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
static const lean_string_object l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value;
lean_object* lean_io_prim_handle_get_line(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup-file"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-build"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-cache"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__8_value;
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_load_dynlib(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid output from `"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__5_value;
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Lean_determineLakePath();
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_io_prim_handle_get_line(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
lean_inc_ref(x_1);
lean_inc(x_8);
x_11 = lean_apply_2(x_1, x_8, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc_ref(x_1);
lean_inc(x_17);
x_20 = lean_apply_2(x_1, x_17, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = lean_string_append(x_3, x_17);
lean_dec(x_17);
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_3);
return x_26;
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3));
x_2 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_95 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4));
x_96 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
x_97 = lean_array_push(x_96, x_3);
x_98 = lean_array_push(x_97, x_95);
if (x_94 == 2)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7));
x_100 = lean_array_push(x_98, x_99);
x_101 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__8));
x_102 = lean_array_push(x_100, x_101);
x_7 = x_102;
x_8 = lean_box(0);
goto block_93;
}
else
{
x_7 = x_98;
x_8 = lean_box(0);
goto block_93;
}
block_93:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0));
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
x_13 = 1;
x_14 = 0;
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
lean_inc_ref(x_15);
x_16 = lean_io_process_spawn(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_io_process_child_take_stdin(x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instToJsonModuleHeader_toJson(x_4);
x_23 = l_Lean_Json_compress(x_22);
x_24 = l_IO_FS_Handle_putStrLn(x_20, x_23);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_24);
x_25 = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
lean_inc(x_21);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_5);
lean_closure_set(x_26, 2, x_7);
lean_closure_set(x_26, 3, x_21);
lean_closure_set(x_26, 4, x_25);
x_27 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_26);
x_28 = lean_ctor_get(x_21, 1);
x_29 = l_IO_FS_Handle_readToEnd(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_task_get_own(x_27);
x_32 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2));
x_35 = lean_io_process_child_wait(x_34, x_21);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_21, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_21, 0);
lean_dec(x_39);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_string_utf8_byte_size(x_30);
lean_ctor_set(x_21, 2, x_42);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 0, x_30);
x_43 = l_String_Slice_trimAscii(x_21);
lean_dec_ref(x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 2);
lean_inc(x_46);
lean_dec_ref(x_43);
x_47 = lean_string_utf8_extract(x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
x_48 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_33);
x_49 = lean_unbox_uint32(x_41);
lean_dec(x_41);
lean_ctor_set_uint32(x_48, sizeof(void*)*3, x_49);
lean_ctor_set(x_35, 0, x_48);
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint32_t x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_35, 0);
lean_inc(x_50);
lean_dec(x_35);
x_51 = lean_string_utf8_byte_size(x_30);
lean_ctor_set(x_21, 2, x_51);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 0, x_30);
x_52 = l_String_Slice_trimAscii(x_21);
lean_dec_ref(x_21);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = lean_string_utf8_extract(x_53, x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
x_57 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_33);
x_58 = lean_unbox_uint32(x_50);
lean_dec(x_50);
lean_ctor_set_uint32(x_57, sizeof(void*)*3, x_58);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_21);
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_15);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_dec(x_21);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint32_t x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_35, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = lean_string_utf8_byte_size(x_30);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_30);
lean_ctor_set(x_66, 1, x_11);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_String_Slice_trimAscii(x_66);
lean_dec_ref(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 2);
lean_inc(x_70);
lean_dec_ref(x_67);
x_71 = lean_string_utf8_extract(x_68, x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
x_72 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_72, 0, x_15);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_33);
x_73 = lean_unbox_uint32(x_63);
lean_dec(x_63);
lean_ctor_set_uint32(x_72, sizeof(void*)*3, x_73);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_15);
x_75 = lean_ctor_get(x_35, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_76 = x_35;
} else {
 lean_dec_ref(x_35);
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
}
else
{
uint8_t x_78; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec_ref(x_15);
x_78 = !lean_is_exclusive(x_32);
if (x_78 == 0)
{
return x_32;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_32, 0);
lean_inc(x_79);
lean_dec(x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_27);
lean_dec(x_21);
lean_dec_ref(x_15);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
return x_29;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_29, 0);
lean_inc(x_82);
lean_dec(x_29);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_84 = !lean_is_exclusive(x_24);
if (x_84 == 0)
{
return x_24;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_24, 0);
lean_inc(x_85);
lean_dec(x_24);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_18);
if (x_87 == 0)
{
return x_18;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_18, 0);
lean_inc(x_88);
lean_dec(x_18);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_90 = !lean_is_exclusive(x_16);
if (x_90 == 0)
{
return x_16;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_16, 0);
lean_inc(x_91);
lean_dec(x_16);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
x_9 = l_Lean_determineLakePath();
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
x_12 = l_System_FilePath_pathExists(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = lean_box(1);
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_7, x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_39; uint8_t x_40; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get_uint32(x_16, sizeof(void*)*3);
x_20 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_18);
x_24 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
x_25 = lean_array_to_list(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_String_intercalate(x_24, x_26);
x_39 = 0;
x_40 = lean_uint32_dec_eq(x_19, x_39);
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_8);
x_41 = 2;
x_42 = lean_uint32_dec_eq(x_19, x_41);
if (x_42 == 0)
{
uint32_t x_43; uint8_t x_44; 
x_43 = 3;
x_44 = lean_uint32_dec_eq(x_19, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
x_46 = lean_string_append(x_45, x_27);
lean_dec_ref(x_27);
x_47 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_20);
lean_dec_ref(x_20);
x_50 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_21);
lean_dec_ref(x_21);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_11)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_11;
}
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_55 = lean_box(2);
if (lean_is_scalar(x_11)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_11;
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_57 = lean_box(1);
if (lean_is_scalar(x_11)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_11;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_inc_ref(x_20);
x_59 = l_Lean_Json_parse(x_20);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
lean_dec(x_11);
goto block_38;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_instFromJsonModuleSetup_fromJson(x_60);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_68; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_8);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_73 = lean_ctor_get(x_62, 4);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_73);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
x_64 = lean_box(0);
goto block_67;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_box(0);
x_78 = lean_nat_dec_le(x_75, x_75);
if (x_78 == 0)
{
if (x_76 == 0)
{
x_64 = lean_box(0);
goto block_67;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_75);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_73, x_79, x_80, x_77);
x_68 = x_81;
goto block_72;
}
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_75);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_73, x_82, x_83, x_77);
x_68 = x_84;
goto block_72;
}
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_62);
if (lean_is_scalar(x_11)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_11;
}
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
block_72:
{
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
x_64 = lean_box(0);
goto block_67;
}
else
{
uint8_t x_69; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_11);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_11);
goto block_38;
}
}
}
block_38:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
x_29 = lean_string_append(x_28, x_27);
lean_dec_ref(x_27);
x_30 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_20);
lean_dec_ref(x_20);
x_33 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_21);
lean_dec_ref(x_21);
if (lean_is_scalar(x_8)) {
 x_36 = lean_alloc_ctor(3, 1, 0);
} else {
 x_36 = x_8;
 lean_ctor_set_tag(x_36, 3);
}
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_17)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_17;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_15);
if (x_85 == 0)
{
return x_15;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_15, 0);
lean_inc(x_86);
lean_dec(x_15);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
return x_9;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_9, 0);
lean_inc(x_89);
lean_dec(x_9);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_91 = lean_box(1);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_setupFile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__5 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__6 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
