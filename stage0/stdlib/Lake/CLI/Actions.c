// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Init Lake.Build.Run Lake.Build.Targets Lake.CLI.Build
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
static lean_object* l_Lake_Package_resolveDriver___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__5;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_exe___lambda__1(lean_object*);
static lean_object* l_Lake_Package_pack___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_Package_resolveDriver___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__1;
static lean_object* l_Lake_exe___closed__2;
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__2;
static lean_object* l_Lake_Package_test___closed__3;
static lean_object* l_Lake_exe___closed__4;
static lean_object* l_Lake_Package_lint___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___lambda__1___closed__1;
static lean_object* l_Lake_Package_lint___closed__1;
static lean_object* l_Lake_Package_resolveDriver___closed__8;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__1;
static lean_object* l_Lake_exe___closed__3;
static lean_object* l_Lake_Package_uploadRelease___closed__5;
static lean_object* l_Lake_Package_unpack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__5;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
static lean_object* l_Lake_Package_test___closed__1;
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_env___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_LeanExe_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1___boxed__const__1;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___lambda__1___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__6;
static lean_object* l_Lake_Package_resolveDriver___closed__4;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1(lean_object*);
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__2;
static lean_object* l_Lake_Package_resolveDriver___closed__7;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_Package_resolveDriver___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lambda__1___boxed(lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1___boxed(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__7;
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lake_env___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_env(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lake_Workspace_augmentedEnvVars(x_3);
x_6 = lean_box(0);
x_7 = l_Lake_env___closed__1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = lean_io_process_spawn(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_io_process_child_wait(x_7, x_11, x_12);
lean_dec(x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_exe___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_exe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_exe___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown executable `", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_exe___closed__4;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_exe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_findLeanExe_x3f(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = 1;
x_8 = l_Lake_exe___closed__1;
x_9 = l_Lean_Name_toString(x_1, x_7, x_8);
x_10 = l_Lake_exe___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_exe___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_4);
x_18 = l_Lake_Workspace_runFetchM___rarg(x_4, x_17, x_3, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_io_wait(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lake_env(x_26, x_2, x_4, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lake_exe___closed__5;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_exe___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_pack___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packing ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_pack___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_pack___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_5 = l_Lake_Package_pack___closed__1;
x_6 = lean_string_append(x_5, x_2);
x_7 = l_Lake_Package_pack___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_array_push(x_3, x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_System_FilePath_join(x_12, x_14);
lean_dec(x_14);
x_16 = 1;
x_17 = l_Lake_Package_pack___closed__3;
x_18 = l_Lake_tar(x_15, x_2, x_16, x_17, x_11, x_4);
return x_18;
}
}
static lean_object* _init_l_Lake_Package_unpack___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unpacking ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_5 = l_Lake_Package_unpack___closed__1;
x_6 = lean_string_append(x_5, x_2);
x_7 = l_Lake_Package_pack___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_array_push(x_3, x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_System_FilePath_join(x_12, x_14);
lean_dec(x_14);
x_16 = 1;
x_17 = l_Lake_untar(x_2, x_15, x_16, x_11, x_4);
return x_17;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gh", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(0);
x_7 = lean_array_mk(x_1);
x_8 = l_Lake_env___closed__1;
x_9 = l_Lake_Package_uploadRelease___lambda__1___closed__1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_10);
x_12 = l_Lake_proc(x_11, x_10, x_4, x_5);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uploading ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--clobber", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_uploadRelease___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("upload", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-R", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lake_defaultLakeDir;
x_7 = l_System_FilePath_join(x_5, x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 16);
lean_inc(x_9);
x_10 = l_System_FilePath_join(x_7, x_9);
lean_inc(x_10);
x_11 = l_Lake_Package_pack(x_1, x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_Package_uploadRelease___closed__1;
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_Package_uploadRelease___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_9);
lean_dec(x_9);
x_20 = l_Lake_Package_pack___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_push(x_14, x_23);
x_25 = lean_box(0);
x_26 = l_Lake_Package_uploadRelease___closed__4;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lake_Package_uploadRelease___closed__5;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lake_Package_uploadRelease___closed__6;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_array_mk(x_32);
x_34 = lean_ctor_get(x_8, 14);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_8, 13);
lean_inc(x_35);
lean_dec(x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lake_Package_uploadRelease___lambda__1(x_25, x_33, x_36, x_24, x_13);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
x_40 = l_Lake_Package_uploadRelease___closed__7;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_array_mk(x_41);
x_43 = l_Array_append___rarg(x_33, x_42);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = l_Lake_Package_uploadRelease___lambda__1(x_25, x_43, x_44, x_24, x_13);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_25);
x_48 = l_Lake_Package_uploadRelease___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_mk(x_49);
x_51 = l_Array_append___rarg(x_33, x_50);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = l_Lake_Package_uploadRelease___lambda__1(x_25, x_51, x_52, x_24, x_13);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_11, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_11, 0, x_59);
return x_11;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = lean_ctor_get(x_12, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_63 = x_12;
} else {
 lean_dec_ref(x_12);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_uploadRelease___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_Package_resolveDriver___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 47;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___rarg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_Lake_Package_resolveDriver___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" driver '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (too many '/')", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": unknown ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" driver package '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" driver configured", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Lake_exe___closed__1;
x_10 = l_Lean_Name_toString(x_7, x_8, x_9);
x_11 = lean_string_utf8_byte_size(x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_String_split___at_Lake_Package_resolveDriver___spec__1(x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_15 = l_Lake_Package_pack___closed__2;
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
x_17 = l_Lake_Package_resolveDriver___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = l_Lake_Package_resolveDriver___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_3);
x_23 = l_Lake_Package_resolveDriver___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_dec(x_30);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 1, x_29);
lean_ctor_set(x_14, 0, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_dec(x_41);
lean_inc(x_37);
x_42 = l_String_toName(x_37);
x_43 = lean_ctor_get(x_4, 4);
x_44 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_43, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_40);
lean_free_object(x_14);
x_45 = l_Lake_Package_pack___closed__2;
x_46 = lean_string_append(x_45, x_10);
lean_dec(x_10);
x_47 = l_Lake_Package_resolveDriver___closed__4;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_2);
x_50 = l_Lake_Package_resolveDriver___closed__5;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_37);
lean_dec(x_37);
x_53 = l_Lake_Package_resolveDriver___closed__6;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_55);
return x_27;
}
else
{
lean_object* x_56; 
lean_dec(x_37);
lean_dec(x_10);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
lean_dec(x_44);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_40);
lean_ctor_set(x_27, 0, x_56);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
lean_dec(x_27);
lean_inc(x_37);
x_58 = l_String_toName(x_37);
x_59 = lean_ctor_get(x_4, 4);
x_60 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_59, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_57);
lean_free_object(x_14);
x_61 = l_Lake_Package_pack___closed__2;
x_62 = lean_string_append(x_61, x_10);
lean_dec(x_10);
x_63 = l_Lake_Package_resolveDriver___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_2);
x_66 = l_Lake_Package_resolveDriver___closed__5;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_37);
lean_dec(x_37);
x_69 = l_Lake_Package_resolveDriver___closed__6;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_37);
lean_dec(x_10);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
lean_dec(x_60);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_74);
return x_14;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_14, 0);
lean_inc(x_75);
lean_dec(x_14);
x_76 = lean_ctor_get(x_27, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_77 = x_27;
} else {
 lean_dec_ref(x_27);
 x_77 = lean_box(0);
}
lean_inc(x_75);
x_78 = l_String_toName(x_75);
x_79 = lean_ctor_get(x_4, 4);
x_80 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_79, x_78);
lean_dec(x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
x_81 = l_Lake_Package_pack___closed__2;
x_82 = lean_string_append(x_81, x_10);
lean_dec(x_10);
x_83 = l_Lake_Package_resolveDriver___closed__4;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_string_append(x_84, x_2);
x_86 = l_Lake_Package_resolveDriver___closed__5;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_string_append(x_87, x_75);
lean_dec(x_75);
x_89 = l_Lake_Package_resolveDriver___closed__6;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_5);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_10);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec(x_80);
if (lean_is_scalar(x_77)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_77;
 lean_ctor_set_tag(x_94, 0);
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_76);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_27);
lean_dec(x_14);
x_96 = !lean_is_exclusive(x_35);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_35, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_35, 0);
lean_dec(x_98);
x_99 = l_Lake_Package_pack___closed__2;
x_100 = lean_string_append(x_99, x_10);
lean_dec(x_10);
x_101 = l_Lake_Package_resolveDriver___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_2);
x_104 = l_Lake_Package_resolveDriver___closed__2;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_string_append(x_105, x_3);
x_107 = l_Lake_Package_resolveDriver___closed__3;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 0, x_109);
return x_35;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_35);
x_110 = l_Lake_Package_pack___closed__2;
x_111 = lean_string_append(x_110, x_10);
lean_dec(x_10);
x_112 = l_Lake_Package_resolveDriver___closed__1;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_2);
x_115 = l_Lake_Package_resolveDriver___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_3);
x_118 = l_Lake_Package_resolveDriver___closed__3;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_5);
return x_121;
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_1);
x_122 = l_Lake_Package_pack___closed__2;
x_123 = lean_string_append(x_122, x_10);
lean_dec(x_10);
x_124 = l_Lake_Package_resolveDriver___closed__7;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_2);
x_127 = l_Lake_Package_resolveDriver___closed__8;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_5);
return x_130;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_Package_resolveDriver___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_Lake_Package_resolveDriver___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_Lake_Package_resolveDriver___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_resolveDriver(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_test___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid test driver: ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___lambda__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lake_resolveLibTarget(x_5, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_Package_pack___closed__2;
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_Package_test___lambda__1___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lake_CliError_toString(x_10);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_11);
lean_ctor_set_tag(x_8, 18);
lean_ctor_set(x_8, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lake_Package_pack___closed__2;
x_21 = lean_string_append(x_20, x_2);
x_22 = l_Lake_Package_test___lambda__1___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lake_CliError_toString(x_19);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_20);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 7, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_3, 0, x_33);
x_34 = l_Lake_Workspace_runFetchM___rarg(x_5, x_30, x_3, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_wait(x_37, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = l_Lake_Package_test___lambda__1___boxed__const__1;
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lake_Package_test___lambda__1___boxed__const__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_39);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 0);
lean_dec(x_47);
x_48 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_48);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lake_exe___closed__5;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_60 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_dec(x_3);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 1, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 2, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 3, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 4, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 5, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 6, x_62);
x_65 = l_Lake_Workspace_runFetchM___rarg(x_5, x_30, x_64, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_io_wait(x_68, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = l_Lake_Package_test___lambda__1___boxed__const__1;
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_70);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
x_77 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_76;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
static lean_object* _init_l_Lake_Package_test___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid test driver: unknown script, executable, or library '", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": arguments cannot be passed to a library test driver", 53, 53);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 18);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 16);
lean_inc(x_8);
x_9 = l_Lake_Package_test___closed__1;
x_10 = l_Lake_Package_resolveDriver(x_1, x_9, x_8, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Lake_exe___closed__1;
x_21 = l_Lean_Name_toString(x_18, x_19, x_20);
x_22 = lean_ctor_get(x_15, 13);
lean_inc(x_22);
lean_inc(x_16);
x_23 = l_String_toName(x_16);
x_24 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_22, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 9);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_26, x_23);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 8);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_29, x_23);
lean_dec(x_23);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lake_Package_pack___closed__2;
x_32 = lean_string_append(x_31, x_21);
lean_dec(x_21);
x_33 = l_Lake_Package_test___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_16);
lean_dec(x_16);
x_36 = l_Lake_Package_resolveDriver___closed__6;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_38);
return x_10;
}
else
{
uint8_t x_39; 
lean_dec(x_16);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_12, 1, x_40);
x_41 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lake_Package_pack___closed__2;
x_43 = lean_string_append(x_42, x_21);
lean_dec(x_21);
x_44 = l_Lake_Package_test___closed__3;
x_45 = lean_string_append(x_43, x_44);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_45);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
uint8_t x_46; 
x_46 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_47 = l_Lake_Package_pack___closed__2;
x_48 = lean_string_append(x_47, x_21);
lean_dec(x_21);
x_49 = l_Lake_Package_test___closed__3;
x_50 = lean_string_append(x_48, x_49);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_50);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_30);
lean_free_object(x_10);
x_51 = lean_box(0);
x_52 = l_Lake_Package_test___lambda__1(x_12, x_21, x_3, x_51, x_4, x_14);
lean_dec(x_21);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
lean_dec(x_30);
lean_ctor_set(x_12, 1, x_53);
x_54 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = l_Lake_Package_pack___closed__2;
x_56 = lean_string_append(x_55, x_21);
lean_dec(x_21);
x_57 = l_Lake_Package_test___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
uint8_t x_60; 
x_60 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_61 = l_Lake_Package_pack___closed__2;
x_62 = lean_string_append(x_61, x_21);
lean_dec(x_21);
x_63 = l_Lake_Package_test___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_65);
return x_10;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_10);
x_66 = lean_box(0);
x_67 = l_Lake_Package_test___lambda__1(x_12, x_21, x_3, x_66, x_4, x_14);
lean_dec(x_21);
return x_67;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_free_object(x_10);
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
lean_ctor_set(x_12, 1, x_68);
x_69 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_69, 0, x_12);
lean_inc(x_4);
x_70 = l_Lake_Workspace_runFetchM___rarg(x_4, x_69, x_3, x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_io_wait(x_73, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_array_mk(x_2);
x_80 = l_Array_append___rarg(x_7, x_79);
lean_dec(x_79);
x_81 = l_Lake_env(x_78, x_80, x_4, x_76);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_75);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_74, 0);
lean_dec(x_83);
x_84 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_84);
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_dec(x_74);
x_86 = l_Lake_exe___closed__5;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_70);
if (x_88 == 0)
{
return x_70;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_70, 0);
x_90 = lean_ctor_get(x_70, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_70);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_23);
lean_dec(x_21);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_92 = lean_ctor_get(x_24, 0);
lean_inc(x_92);
lean_dec(x_24);
x_93 = lean_array_to_list(x_7);
x_94 = l_List_appendTR___rarg(x_93, x_2);
x_95 = l_Lake_Script_run(x_94, x_92, x_4, x_14);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_96 = lean_ctor_get(x_10, 1);
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_ctor_get(x_97, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 2);
lean_inc(x_100);
lean_dec(x_99);
x_101 = 0;
x_102 = l_Lake_exe___closed__1;
x_103 = l_Lean_Name_toString(x_100, x_101, x_102);
x_104 = lean_ctor_get(x_97, 13);
lean_inc(x_104);
lean_inc(x_98);
x_105 = l_String_toName(x_98);
x_106 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_104, x_105);
lean_dec(x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_97, 9);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_108, x_105);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_97, 8);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_111, x_105);
lean_dec(x_105);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = l_Lake_Package_pack___closed__2;
x_114 = lean_string_append(x_113, x_103);
lean_dec(x_103);
x_115 = l_Lake_Package_test___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_98);
lean_dec(x_98);
x_118 = l_Lake_Package_resolveDriver___closed__6;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_120);
return x_10;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_98);
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_122 = x_112;
} else {
 lean_dec_ref(x_112);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_97);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_123);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = l_Lake_Package_pack___closed__2;
x_126 = lean_string_append(x_125, x_103);
lean_dec(x_103);
x_127 = l_Lake_Package_test___closed__3;
x_128 = lean_string_append(x_126, x_127);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(18, 1, 0);
} else {
 x_129 = x_122;
 lean_ctor_set_tag(x_129, 18);
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_129);
return x_10;
}
else
{
uint8_t x_130; 
x_130 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_123);
lean_dec(x_4);
lean_dec(x_3);
x_131 = l_Lake_Package_pack___closed__2;
x_132 = lean_string_append(x_131, x_103);
lean_dec(x_103);
x_133 = l_Lake_Package_test___closed__3;
x_134 = lean_string_append(x_132, x_133);
if (lean_is_scalar(x_122)) {
 x_135 = lean_alloc_ctor(18, 1, 0);
} else {
 x_135 = x_122;
 lean_ctor_set_tag(x_135, 18);
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_135);
return x_10;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_122);
lean_free_object(x_10);
x_136 = lean_box(0);
x_137 = l_Lake_Package_test___lambda__1(x_123, x_103, x_3, x_136, x_4, x_96);
lean_dec(x_103);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_98);
lean_free_object(x_10);
x_138 = lean_ctor_get(x_109, 0);
lean_inc(x_138);
lean_dec(x_109);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_97);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_140, 0, x_139);
lean_inc(x_4);
x_141 = l_Lake_Workspace_runFetchM___rarg(x_4, x_140, x_3, x_96);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_io_wait(x_144, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_array_mk(x_2);
x_151 = l_Array_append___rarg(x_7, x_150);
lean_dec(x_150);
x_152 = l_Lake_env(x_149, x_151, x_4, x_147);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_154 = x_145;
} else {
 lean_dec_ref(x_145);
 x_154 = lean_box(0);
}
x_155 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_154;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_157 = lean_ctor_get(x_141, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_free_object(x_10);
lean_dec(x_3);
x_161 = lean_ctor_get(x_106, 0);
lean_inc(x_161);
lean_dec(x_106);
x_162 = lean_array_to_list(x_7);
x_163 = l_List_appendTR___rarg(x_162, x_2);
x_164 = l_Lake_Script_run(x_163, x_161, x_4, x_96);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_165 = lean_ctor_get(x_10, 0);
x_166 = lean_ctor_get(x_10, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_10);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_169 = x_165;
} else {
 lean_dec_ref(x_165);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_167, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 2);
lean_inc(x_171);
lean_dec(x_170);
x_172 = 0;
x_173 = l_Lake_exe___closed__1;
x_174 = l_Lean_Name_toString(x_171, x_172, x_173);
x_175 = lean_ctor_get(x_167, 13);
lean_inc(x_175);
lean_inc(x_168);
x_176 = l_String_toName(x_168);
x_177 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_175, x_176);
lean_dec(x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_167, 9);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_179, x_176);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_167, 8);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_182, x_176);
lean_dec(x_176);
lean_dec(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = l_Lake_Package_pack___closed__2;
x_185 = lean_string_append(x_184, x_174);
lean_dec(x_174);
x_186 = l_Lake_Package_test___closed__2;
x_187 = lean_string_append(x_185, x_186);
x_188 = lean_string_append(x_187, x_168);
lean_dec(x_168);
x_189 = l_Lake_Package_resolveDriver___closed__6;
x_190 = lean_string_append(x_188, x_189);
x_191 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_166);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_168);
x_193 = lean_ctor_get(x_183, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_194 = x_183;
} else {
 lean_dec_ref(x_183);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_169;
}
lean_ctor_set(x_195, 0, x_167);
lean_ctor_set(x_195, 1, x_193);
x_196 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_195);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = l_Lake_Package_pack___closed__2;
x_198 = lean_string_append(x_197, x_174);
lean_dec(x_174);
x_199 = l_Lake_Package_test___closed__3;
x_200 = lean_string_append(x_198, x_199);
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(18, 1, 0);
} else {
 x_201 = x_194;
 lean_ctor_set_tag(x_201, 18);
}
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_166);
return x_202;
}
else
{
uint8_t x_203; 
x_203 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_195);
lean_dec(x_4);
lean_dec(x_3);
x_204 = l_Lake_Package_pack___closed__2;
x_205 = lean_string_append(x_204, x_174);
lean_dec(x_174);
x_206 = l_Lake_Package_test___closed__3;
x_207 = lean_string_append(x_205, x_206);
if (lean_is_scalar(x_194)) {
 x_208 = lean_alloc_ctor(18, 1, 0);
} else {
 x_208 = x_194;
 lean_ctor_set_tag(x_208, 18);
}
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_166);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_194);
x_210 = lean_box(0);
x_211 = l_Lake_Package_test___lambda__1(x_195, x_174, x_3, x_210, x_4, x_166);
lean_dec(x_174);
return x_211;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_168);
x_212 = lean_ctor_get(x_180, 0);
lean_inc(x_212);
lean_dec(x_180);
if (lean_is_scalar(x_169)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_169;
}
lean_ctor_set(x_213, 0, x_167);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_214, 0, x_213);
lean_inc(x_4);
x_215 = l_Lake_Workspace_runFetchM___rarg(x_4, x_214, x_3, x_166);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_io_wait(x_218, x_217);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_array_mk(x_2);
x_225 = l_Array_append___rarg(x_7, x_224);
lean_dec(x_224);
x_226 = l_Lake_env(x_223, x_225, x_4, x_221);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_220);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_227 = lean_ctor_get(x_219, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_228 = x_219;
} else {
 lean_dec_ref(x_219);
 x_228 = lean_box(0);
}
x_229 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_228;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_231 = lean_ctor_get(x_215, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_215, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_233 = x_215;
} else {
 lean_dec_ref(x_215);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_3);
x_235 = lean_ctor_get(x_177, 0);
lean_inc(x_235);
lean_dec(x_177);
x_236 = lean_array_to_list(x_7);
x_237 = l_List_appendTR___rarg(x_236, x_2);
x_238 = l_Lake_Script_run(x_237, x_235, x_4, x_166);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_239 = !lean_is_exclusive(x_10);
if (x_239 == 0)
{
return x_10;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_10, 0);
x_241 = lean_ctor_get(x_10, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_10);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Package_test___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lake_Package_lint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lint", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_lint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid lint driver: unknown script or executable '", 53, 53);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 20);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 17);
lean_inc(x_8);
x_9 = l_Lake_Package_lint___closed__1;
x_10 = l_Lake_Package_resolveDriver(x_1, x_9, x_8, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_15, 13);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_String_toName(x_16);
x_19 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_17, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_21, x_18);
lean_dec(x_18);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Lake_exe___closed__1;
x_27 = l_Lean_Name_toString(x_24, x_25, x_26);
x_28 = l_Lake_Package_pack___closed__2;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lake_Package_lint___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_16);
lean_dec(x_16);
x_33 = l_Lake_Package_resolveDriver___closed__6;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_35);
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_free_object(x_10);
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
lean_dec(x_22);
lean_ctor_set(x_12, 1, x_36);
x_37 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_37, 0, x_12);
lean_inc(x_4);
x_38 = l_Lake_Workspace_runFetchM___rarg(x_4, x_37, x_3, x_14);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_io_wait(x_41, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_array_mk(x_2);
x_48 = l_Array_append___rarg(x_7, x_47);
lean_dec(x_47);
x_49 = l_Lake_env(x_46, x_48, x_4, x_44);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_43);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_42, 0);
lean_dec(x_51);
x_52 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_52);
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_dec(x_42);
x_54 = l_Lake_exe___closed__5;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_60 = lean_ctor_get(x_19, 0);
lean_inc(x_60);
lean_dec(x_19);
x_61 = lean_array_to_list(x_7);
x_62 = l_List_appendTR___rarg(x_61, x_2);
x_63 = l_Lake_Script_run(x_62, x_60, x_4, x_14);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_10, 1);
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_ctor_get(x_65, 13);
lean_inc(x_67);
lean_inc(x_66);
x_68 = l_String_toName(x_66);
x_69 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_67, x_68);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 9);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_71, x_68);
lean_dec(x_68);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_65, 2);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
lean_dec(x_73);
x_75 = 0;
x_76 = l_Lake_exe___closed__1;
x_77 = l_Lean_Name_toString(x_74, x_75, x_76);
x_78 = l_Lake_Package_pack___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lake_Package_lint___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_66);
lean_dec(x_66);
x_83 = l_Lake_Package_resolveDriver___closed__6;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_85);
return x_10;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_free_object(x_10);
x_86 = lean_ctor_get(x_72, 0);
lean_inc(x_86);
lean_dec(x_72);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_65);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_88, 0, x_87);
lean_inc(x_4);
x_89 = l_Lake_Workspace_runFetchM___rarg(x_4, x_88, x_3, x_64);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_io_wait(x_92, x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_array_mk(x_2);
x_99 = l_Array_append___rarg(x_7, x_98);
lean_dec(x_98);
x_100 = l_Lake_env(x_97, x_99, x_4, x_95);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
x_103 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_102;
 lean_ctor_set_tag(x_104, 1);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_105 = lean_ctor_get(x_89, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_107 = x_89;
} else {
 lean_dec_ref(x_89);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_10);
lean_dec(x_3);
x_109 = lean_ctor_get(x_69, 0);
lean_inc(x_109);
lean_dec(x_69);
x_110 = lean_array_to_list(x_7);
x_111 = l_List_appendTR___rarg(x_110, x_2);
x_112 = l_Lake_Script_run(x_111, x_109, x_4, x_64);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_10, 0);
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_10);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_115, 13);
lean_inc(x_118);
lean_inc(x_116);
x_119 = l_String_toName(x_116);
x_120 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_118, x_119);
lean_dec(x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_115, 9);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_122, x_119);
lean_dec(x_119);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_115, 2);
lean_inc(x_124);
lean_dec(x_115);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
lean_dec(x_124);
x_126 = 0;
x_127 = l_Lake_exe___closed__1;
x_128 = l_Lean_Name_toString(x_125, x_126, x_127);
x_129 = l_Lake_Package_pack___closed__2;
x_130 = lean_string_append(x_129, x_128);
lean_dec(x_128);
x_131 = l_Lake_Package_lint___closed__2;
x_132 = lean_string_append(x_130, x_131);
x_133 = lean_string_append(x_132, x_116);
lean_dec(x_116);
x_134 = l_Lake_Package_resolveDriver___closed__6;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_114);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_116);
x_138 = lean_ctor_get(x_123, 0);
lean_inc(x_138);
lean_dec(x_123);
if (lean_is_scalar(x_117)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_117;
}
lean_ctor_set(x_139, 0, x_115);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_140, 0, x_139);
lean_inc(x_4);
x_141 = l_Lake_Workspace_runFetchM___rarg(x_4, x_140, x_3, x_114);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_io_wait(x_144, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_array_mk(x_2);
x_151 = l_Array_append___rarg(x_7, x_150);
lean_dec(x_150);
x_152 = l_Lake_env(x_149, x_151, x_4, x_147);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_154 = x_145;
} else {
 lean_dec_ref(x_145);
 x_154 = lean_box(0);
}
x_155 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_154;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_157 = lean_ctor_get(x_141, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_3);
x_161 = lean_ctor_get(x_120, 0);
lean_inc(x_161);
lean_dec(x_120);
x_162 = lean_array_to_list(x_7);
x_163 = l_List_appendTR___rarg(x_162, x_2);
x_164 = l_Lake_Script_run(x_163, x_161, x_4, x_114);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_10);
if (x_165 == 0)
{
return x_10;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_10, 0);
x_167 = lean_ctor_get(x_10, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_10);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_env___closed__1 = _init_l_Lake_env___closed__1();
lean_mark_persistent(l_Lake_env___closed__1);
l_Lake_exe___closed__1 = _init_l_Lake_exe___closed__1();
lean_mark_persistent(l_Lake_exe___closed__1);
l_Lake_exe___closed__2 = _init_l_Lake_exe___closed__2();
lean_mark_persistent(l_Lake_exe___closed__2);
l_Lake_exe___closed__3 = _init_l_Lake_exe___closed__3();
lean_mark_persistent(l_Lake_exe___closed__3);
l_Lake_exe___closed__4 = _init_l_Lake_exe___closed__4();
lean_mark_persistent(l_Lake_exe___closed__4);
l_Lake_exe___closed__5 = _init_l_Lake_exe___closed__5();
lean_mark_persistent(l_Lake_exe___closed__5);
l_Lake_Package_pack___closed__1 = _init_l_Lake_Package_pack___closed__1();
lean_mark_persistent(l_Lake_Package_pack___closed__1);
l_Lake_Package_pack___closed__2 = _init_l_Lake_Package_pack___closed__2();
lean_mark_persistent(l_Lake_Package_pack___closed__2);
l_Lake_Package_pack___closed__3 = _init_l_Lake_Package_pack___closed__3();
lean_mark_persistent(l_Lake_Package_pack___closed__3);
l_Lake_Package_unpack___closed__1 = _init_l_Lake_Package_unpack___closed__1();
lean_mark_persistent(l_Lake_Package_unpack___closed__1);
l_Lake_Package_uploadRelease___lambda__1___closed__1 = _init_l_Lake_Package_uploadRelease___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_uploadRelease___lambda__1___closed__1);
l_Lake_Package_uploadRelease___closed__1 = _init_l_Lake_Package_uploadRelease___closed__1();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__1);
l_Lake_Package_uploadRelease___closed__2 = _init_l_Lake_Package_uploadRelease___closed__2();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__2);
l_Lake_Package_uploadRelease___closed__3 = _init_l_Lake_Package_uploadRelease___closed__3();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__3);
l_Lake_Package_uploadRelease___closed__4 = _init_l_Lake_Package_uploadRelease___closed__4();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__4);
l_Lake_Package_uploadRelease___closed__5 = _init_l_Lake_Package_uploadRelease___closed__5();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__5);
l_Lake_Package_uploadRelease___closed__6 = _init_l_Lake_Package_uploadRelease___closed__6();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__6);
l_Lake_Package_uploadRelease___closed__7 = _init_l_Lake_Package_uploadRelease___closed__7();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__7);
l_Lake_Package_resolveDriver___closed__1 = _init_l_Lake_Package_resolveDriver___closed__1();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__1);
l_Lake_Package_resolveDriver___closed__2 = _init_l_Lake_Package_resolveDriver___closed__2();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__2);
l_Lake_Package_resolveDriver___closed__3 = _init_l_Lake_Package_resolveDriver___closed__3();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__3);
l_Lake_Package_resolveDriver___closed__4 = _init_l_Lake_Package_resolveDriver___closed__4();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__4);
l_Lake_Package_resolveDriver___closed__5 = _init_l_Lake_Package_resolveDriver___closed__5();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__5);
l_Lake_Package_resolveDriver___closed__6 = _init_l_Lake_Package_resolveDriver___closed__6();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__6);
l_Lake_Package_resolveDriver___closed__7 = _init_l_Lake_Package_resolveDriver___closed__7();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__7);
l_Lake_Package_resolveDriver___closed__8 = _init_l_Lake_Package_resolveDriver___closed__8();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__8);
l_Lake_Package_test___lambda__1___closed__1 = _init_l_Lake_Package_test___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_test___lambda__1___closed__1);
l_Lake_Package_test___lambda__1___boxed__const__1 = _init_l_Lake_Package_test___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lake_Package_test___lambda__1___boxed__const__1);
l_Lake_Package_test___closed__1 = _init_l_Lake_Package_test___closed__1();
lean_mark_persistent(l_Lake_Package_test___closed__1);
l_Lake_Package_test___closed__2 = _init_l_Lake_Package_test___closed__2();
lean_mark_persistent(l_Lake_Package_test___closed__2);
l_Lake_Package_test___closed__3 = _init_l_Lake_Package_test___closed__3();
lean_mark_persistent(l_Lake_Package_test___closed__3);
l_Lake_Package_lint___closed__1 = _init_l_Lake_Package_lint___closed__1();
lean_mark_persistent(l_Lake_Package_lint___closed__1);
l_Lake_Package_lint___closed__2 = _init_l_Lake_Package_lint___closed__2();
lean_mark_persistent(l_Lake_Package_lint___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
