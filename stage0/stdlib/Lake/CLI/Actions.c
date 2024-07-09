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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__9;
lean_object* lean_array_data(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__10;
static lean_object* l_Lake_Package_pack___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
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
static lean_object* l_Lake_Package_resolveDriver___closed__2;
static lean_object* l_Lake_Package_test___closed__3;
static lean_object* l_Lake_exe___closed__4;
static lean_object* l_Lake_Package_lint___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Lake_Package_test___lambda__1___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__8;
static lean_object* l_Lake_Package_lint___closed__1;
static lean_object* l_Lake_Package_resolveDriver___closed__8;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__1;
static lean_object* l_Lake_exe___closed__3;
static lean_object* l_Lake_Package_uploadRelease___closed__5;
static lean_object* l_Lake_Package_unpack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__11;
static lean_object* l_Lake_Package_uploadRelease___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__5;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
static lean_object* l_Lake_Package_test___closed__1;
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_env___closed__1;
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
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1(lean_object*);
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__2;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__12;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_Package_resolveDriver___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_Lake_Package_resolveDriver___spec__1___boxed(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__7;
LEAN_EXPORT lean_object* l_Lake_Package_test___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_exe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown executable `", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_exe___closed__3;
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_1, x_7);
x_9 = l_Lake_exe___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_exe___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_4);
x_17 = l_Lake_Workspace_runFetchM___rarg(x_4, x_16, x_3, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_wait(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lake_env(x_25, x_2, x_4, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_dec(x_28);
x_29 = l_Lake_exe___closed__4;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_Lake_exe___closed__4;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_box(0);
x_6 = l_Lake_env___closed__1;
x_7 = l_Lake_Package_uploadRelease___lambda__1___closed__1;
x_8 = l_Lake_Package_pack___closed__3;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = l_Lake_proc(x_10, x_9, x_3, x_4);
return x_11;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__3;
x_2 = l_Lake_Package_uploadRelease___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("upload", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__5;
x_2 = l_Lake_Package_uploadRelease___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--clobber", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_uploadRelease___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-R", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__10;
x_2 = l_Lake_Package_uploadRelease___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
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
lean_inc(x_9);
x_10 = l_System_FilePath_join(x_7, x_9);
lean_inc(x_10);
x_11 = l_Lake_Package_pack(x_1, x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_25 = l_Lake_Package_uploadRelease___closed__7;
x_26 = lean_array_push(x_25, x_2);
x_27 = lean_array_push(x_26, x_10);
x_28 = l_Lake_Package_uploadRelease___closed__8;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lake_Package_uploadRelease___closed__9;
x_31 = lean_ctor_get(x_8, 14);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_8, 13);
lean_inc(x_32);
lean_dec(x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_apply_4(x_30, x_29, x_33, x_24, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lake_Package_uploadRelease___closed__12;
x_37 = lean_array_push(x_36, x_35);
x_38 = l_Array_append___rarg(x_29, x_37);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_apply_4(x_30, x_38, x_39, x_24, x_13);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = l_Lake_Package_uploadRelease___closed__12;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Array_append___rarg(x_29, x_43);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = lean_apply_4(x_30, x_44, x_45, x_24, x_13);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_11, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_11, 0, x_52);
return x_11;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_56 = x_12;
} else {
 lean_dec_ref(x_12);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_uploadRelease___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = l_String_isEmpty(x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_String_split___at_Lake_Package_resolveDriver___spec__1(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_12 = l_Lake_Package_pack___closed__2;
x_13 = lean_string_append(x_12, x_9);
lean_dec(x_9);
x_14 = l_Lake_Package_resolveDriver___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_Package_resolveDriver___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_3);
x_20 = l_Lake_Package_resolveDriver___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_dec(x_27);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 1, x_26);
lean_ctor_set(x_11, 0, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
lean_inc(x_34);
x_39 = l_String_toName(x_34);
x_40 = lean_ctor_get(x_4, 3);
x_41 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_40, x_39);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_free_object(x_11);
x_42 = l_Lake_Package_pack___closed__2;
x_43 = lean_string_append(x_42, x_9);
lean_dec(x_9);
x_44 = l_Lake_Package_resolveDriver___closed__4;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_2);
x_47 = l_Lake_Package_resolveDriver___closed__5;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_34);
lean_dec(x_34);
x_50 = l_Lake_Package_resolveDriver___closed__6;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 0, x_52);
return x_24;
}
else
{
lean_object* x_53; 
lean_dec(x_34);
lean_dec(x_9);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_53);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_24, 0);
lean_inc(x_54);
lean_dec(x_24);
lean_inc(x_34);
x_55 = l_String_toName(x_34);
x_56 = lean_ctor_get(x_4, 3);
x_57 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_56, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
lean_free_object(x_11);
x_58 = l_Lake_Package_pack___closed__2;
x_59 = lean_string_append(x_58, x_9);
lean_dec(x_9);
x_60 = l_Lake_Package_resolveDriver___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_2);
x_63 = l_Lake_Package_resolveDriver___closed__5;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_34);
lean_dec(x_34);
x_66 = l_Lake_Package_resolveDriver___closed__6;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
lean_dec(x_9);
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_71);
return x_11;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_11, 0);
lean_inc(x_72);
lean_dec(x_11);
x_73 = lean_ctor_get(x_24, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_74 = x_24;
} else {
 lean_dec_ref(x_24);
 x_74 = lean_box(0);
}
lean_inc(x_72);
x_75 = l_String_toName(x_72);
x_76 = lean_ctor_get(x_4, 3);
x_77 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_76, x_75);
lean_dec(x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_73);
x_78 = l_Lake_Package_pack___closed__2;
x_79 = lean_string_append(x_78, x_9);
lean_dec(x_9);
x_80 = l_Lake_Package_resolveDriver___closed__4;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_2);
x_83 = l_Lake_Package_resolveDriver___closed__5;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_string_append(x_84, x_72);
lean_dec(x_72);
x_86 = l_Lake_Package_resolveDriver___closed__6;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_74)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_74;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_72);
lean_dec(x_9);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
lean_dec(x_77);
if (lean_is_scalar(x_74)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_74;
 lean_ctor_set_tag(x_91, 0);
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_73);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_5);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_24);
lean_dec(x_11);
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_ctor_get(x_32, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_32, 0);
lean_dec(x_95);
x_96 = l_Lake_Package_pack___closed__2;
x_97 = lean_string_append(x_96, x_9);
lean_dec(x_9);
x_98 = l_Lake_Package_resolveDriver___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_string_append(x_99, x_2);
x_101 = l_Lake_Package_resolveDriver___closed__2;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_3);
x_104 = l_Lake_Package_resolveDriver___closed__3;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set(x_32, 0, x_106);
return x_32;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_32);
x_107 = l_Lake_Package_pack___closed__2;
x_108 = lean_string_append(x_107, x_9);
lean_dec(x_9);
x_109 = l_Lake_Package_resolveDriver___closed__1;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_string_append(x_110, x_2);
x_112 = l_Lake_Package_resolveDriver___closed__2;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_3);
x_115 = l_Lake_Package_resolveDriver___closed__3;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_5);
return x_118;
}
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_1);
x_119 = l_Lake_Package_pack___closed__2;
x_120 = lean_string_append(x_119, x_9);
lean_dec(x_9);
x_121 = l_Lake_Package_resolveDriver___closed__7;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_2);
x_124 = l_Lake_Package_resolveDriver___closed__8;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
return x_127;
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
x_48 = l_Lake_exe___closed__4;
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
x_50 = l_Lake_exe___closed__4;
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
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_60 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
lean_dec(x_3);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_56);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 1, x_57);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 2, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 3, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 4, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 5, x_61);
x_64 = l_Lake_Workspace_runFetchM___rarg(x_5, x_30, x_63, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_io_wait(x_67, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Package_test___lambda__1___boxed__const__1;
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_69);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
x_76 = l_Lake_exe___closed__4;
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_80 = x_64;
} else {
 lean_dec_ref(x_64);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Lean_Name_toString(x_18, x_19);
x_21 = lean_ctor_get(x_15, 13);
lean_inc(x_21);
lean_inc(x_16);
x_22 = l_String_toName(x_16);
x_23 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_21, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 9);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_25, x_22);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 8);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lake_Package_pack___closed__2;
x_31 = lean_string_append(x_30, x_20);
lean_dec(x_20);
x_32 = l_Lake_Package_test___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_16);
lean_dec(x_16);
x_35 = l_Lake_Package_resolveDriver___closed__6;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_37);
return x_10;
}
else
{
uint8_t x_38; 
lean_dec(x_16);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_12, 1, x_39);
x_40 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Lake_Package_pack___closed__2;
x_42 = lean_string_append(x_41, x_20);
lean_dec(x_20);
x_43 = l_Lake_Package_test___closed__3;
x_44 = lean_string_append(x_42, x_43);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_44);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_29);
return x_10;
}
else
{
uint8_t x_45; 
x_45 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_46 = l_Lake_Package_pack___closed__2;
x_47 = lean_string_append(x_46, x_20);
lean_dec(x_20);
x_48 = l_Lake_Package_test___closed__3;
x_49 = lean_string_append(x_47, x_48);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_49);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_29);
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_29);
lean_free_object(x_10);
x_50 = lean_box(0);
x_51 = l_Lake_Package_test___lambda__1(x_12, x_20, x_3, x_50, x_4, x_14);
lean_dec(x_20);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_29, 0);
lean_inc(x_52);
lean_dec(x_29);
lean_ctor_set(x_12, 1, x_52);
x_53 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = l_Lake_Package_pack___closed__2;
x_55 = lean_string_append(x_54, x_20);
lean_dec(x_20);
x_56 = l_Lake_Package_test___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
else
{
uint8_t x_59; 
x_59 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_60 = l_Lake_Package_pack___closed__2;
x_61 = lean_string_append(x_60, x_20);
lean_dec(x_20);
x_62 = l_Lake_Package_test___closed__3;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_64);
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_free_object(x_10);
x_65 = lean_box(0);
x_66 = l_Lake_Package_test___lambda__1(x_12, x_20, x_3, x_65, x_4, x_14);
lean_dec(x_20);
return x_66;
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_16);
lean_free_object(x_10);
x_67 = lean_ctor_get(x_26, 0);
lean_inc(x_67);
lean_dec(x_26);
lean_ctor_set(x_12, 1, x_67);
x_68 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_68, 0, x_12);
lean_inc(x_4);
x_69 = l_Lake_Workspace_runFetchM___rarg(x_4, x_68, x_3, x_14);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_io_wait(x_72, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_List_redLength___rarg(x_2);
x_79 = lean_mk_empty_array_with_capacity(x_78);
lean_dec(x_78);
x_80 = l_List_toArrayAux___rarg(x_2, x_79);
x_81 = l_Array_append___rarg(x_7, x_80);
lean_dec(x_80);
x_82 = l_Lake_env(x_77, x_81, x_4, x_75);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_73);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_73, 0);
lean_dec(x_84);
x_85 = l_Lake_exe___closed__4;
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_85);
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
x_87 = l_Lake_exe___closed__4;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_69);
if (x_89 == 0)
{
return x_69;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_69, 0);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_69);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_22);
lean_dec(x_20);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_93 = lean_ctor_get(x_23, 0);
lean_inc(x_93);
lean_dec(x_23);
x_94 = lean_array_to_list(lean_box(0), x_7);
x_95 = l_List_appendTR___rarg(x_94, x_2);
x_96 = l_Lake_Script_run(x_95, x_93, x_4, x_14);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_10, 1);
x_98 = lean_ctor_get(x_12, 0);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_12);
x_100 = lean_ctor_get(x_98, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
lean_dec(x_100);
x_102 = 0;
x_103 = l_Lean_Name_toString(x_101, x_102);
x_104 = lean_ctor_get(x_98, 13);
lean_inc(x_104);
lean_inc(x_99);
x_105 = l_String_toName(x_99);
x_106 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_104, x_105);
lean_dec(x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 9);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_108, x_105);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_98, 8);
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
lean_dec(x_98);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = l_Lake_Package_pack___closed__2;
x_114 = lean_string_append(x_113, x_103);
lean_dec(x_103);
x_115 = l_Lake_Package_test___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_99);
lean_dec(x_99);
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
lean_dec(x_99);
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
lean_ctor_set(x_123, 0, x_98);
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
x_137 = l_Lake_Package_test___lambda__1(x_123, x_103, x_3, x_136, x_4, x_97);
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
lean_dec(x_99);
lean_free_object(x_10);
x_138 = lean_ctor_get(x_109, 0);
lean_inc(x_138);
lean_dec(x_109);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_98);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_140, 0, x_139);
lean_inc(x_4);
x_141 = l_Lake_Workspace_runFetchM___rarg(x_4, x_140, x_3, x_97);
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
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_List_redLength___rarg(x_2);
x_151 = lean_mk_empty_array_with_capacity(x_150);
lean_dec(x_150);
x_152 = l_List_toArrayAux___rarg(x_2, x_151);
x_153 = l_Array_append___rarg(x_7, x_152);
lean_dec(x_152);
x_154 = l_Lake_env(x_149, x_153, x_4, x_147);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_155 = lean_ctor_get(x_145, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_156 = x_145;
} else {
 lean_dec_ref(x_145);
 x_156 = lean_box(0);
}
x_157 = l_Lake_exe___closed__4;
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_156;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_159 = lean_ctor_get(x_141, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_141, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_161 = x_141;
} else {
 lean_dec_ref(x_141);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_10);
lean_dec(x_3);
x_163 = lean_ctor_get(x_106, 0);
lean_inc(x_163);
lean_dec(x_106);
x_164 = lean_array_to_list(lean_box(0), x_7);
x_165 = l_List_appendTR___rarg(x_164, x_2);
x_166 = l_Lake_Script_run(x_165, x_163, x_4, x_97);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_167 = lean_ctor_get(x_10, 0);
x_168 = lean_ctor_get(x_10, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_10);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_169, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 2);
lean_inc(x_173);
lean_dec(x_172);
x_174 = 0;
x_175 = l_Lean_Name_toString(x_173, x_174);
x_176 = lean_ctor_get(x_169, 13);
lean_inc(x_176);
lean_inc(x_170);
x_177 = l_String_toName(x_170);
x_178 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_176, x_177);
lean_dec(x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_169, 9);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_180, x_177);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_169, 8);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_183, x_177);
lean_dec(x_177);
lean_dec(x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = l_Lake_Package_pack___closed__2;
x_186 = lean_string_append(x_185, x_175);
lean_dec(x_175);
x_187 = l_Lake_Package_test___closed__2;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_170);
lean_dec(x_170);
x_190 = l_Lake_Package_resolveDriver___closed__6;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_168);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_170);
x_194 = lean_ctor_get(x_184, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_195 = x_184;
} else {
 lean_dec_ref(x_184);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_171;
}
lean_ctor_set(x_196, 0, x_169);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = l_Lake_Package_pack___closed__2;
x_199 = lean_string_append(x_198, x_175);
lean_dec(x_175);
x_200 = l_Lake_Package_test___closed__3;
x_201 = lean_string_append(x_199, x_200);
if (lean_is_scalar(x_195)) {
 x_202 = lean_alloc_ctor(18, 1, 0);
} else {
 x_202 = x_195;
 lean_ctor_set_tag(x_202, 18);
}
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_168);
return x_203;
}
else
{
uint8_t x_204; 
x_204 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_196);
lean_dec(x_4);
lean_dec(x_3);
x_205 = l_Lake_Package_pack___closed__2;
x_206 = lean_string_append(x_205, x_175);
lean_dec(x_175);
x_207 = l_Lake_Package_test___closed__3;
x_208 = lean_string_append(x_206, x_207);
if (lean_is_scalar(x_195)) {
 x_209 = lean_alloc_ctor(18, 1, 0);
} else {
 x_209 = x_195;
 lean_ctor_set_tag(x_209, 18);
}
lean_ctor_set(x_209, 0, x_208);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_168);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_195);
x_211 = lean_box(0);
x_212 = l_Lake_Package_test___lambda__1(x_196, x_175, x_3, x_211, x_4, x_168);
lean_dec(x_175);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_170);
x_213 = lean_ctor_get(x_181, 0);
lean_inc(x_213);
lean_dec(x_181);
if (lean_is_scalar(x_171)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_171;
}
lean_ctor_set(x_214, 0, x_169);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_215, 0, x_214);
lean_inc(x_4);
x_216 = l_Lake_Workspace_runFetchM___rarg(x_4, x_215, x_3, x_168);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_io_wait(x_219, x_218);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_List_redLength___rarg(x_2);
x_226 = lean_mk_empty_array_with_capacity(x_225);
lean_dec(x_225);
x_227 = l_List_toArrayAux___rarg(x_2, x_226);
x_228 = l_Array_append___rarg(x_7, x_227);
lean_dec(x_227);
x_229 = l_Lake_env(x_224, x_228, x_4, x_222);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_221);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_230 = lean_ctor_get(x_220, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_231 = x_220;
} else {
 lean_dec_ref(x_220);
 x_231 = lean_box(0);
}
x_232 = l_Lake_exe___closed__4;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_231;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_234 = lean_ctor_get(x_216, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_216, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_3);
x_238 = lean_ctor_get(x_178, 0);
lean_inc(x_238);
lean_dec(x_178);
x_239 = lean_array_to_list(lean_box(0), x_7);
x_240 = l_List_appendTR___rarg(x_239, x_2);
x_241 = l_Lake_Script_run(x_240, x_238, x_4, x_168);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_10);
if (x_242 == 0)
{
return x_10;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_10, 0);
x_244 = lean_ctor_get(x_10, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_10);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_26 = l_Lean_Name_toString(x_24, x_25);
x_27 = l_Lake_Package_pack___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lake_Package_lint___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_16);
lean_dec(x_16);
x_32 = l_Lake_Package_resolveDriver___closed__6;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_34);
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
lean_free_object(x_10);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
lean_ctor_set(x_12, 1, x_35);
x_36 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_36, 0, x_12);
lean_inc(x_4);
x_37 = l_Lake_Workspace_runFetchM___rarg(x_4, x_36, x_3, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_io_wait(x_40, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_List_redLength___rarg(x_2);
x_47 = lean_mk_empty_array_with_capacity(x_46);
lean_dec(x_46);
x_48 = l_List_toArrayAux___rarg(x_2, x_47);
x_49 = l_Array_append___rarg(x_7, x_48);
lean_dec(x_48);
x_50 = l_Lake_env(x_45, x_49, x_4, x_43);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_41, 0);
lean_dec(x_52);
x_53 = l_Lake_exe___closed__4;
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_53);
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lake_exe___closed__4;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_37);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_61 = lean_ctor_get(x_19, 0);
lean_inc(x_61);
lean_dec(x_19);
x_62 = lean_array_data(x_7);
x_63 = l_List_appendTR___rarg(x_62, x_2);
x_64 = l_Lake_Script_run(x_63, x_61, x_4, x_14);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_10, 1);
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_ctor_get(x_66, 13);
lean_inc(x_68);
lean_inc(x_67);
x_69 = l_String_toName(x_67);
x_70 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_68, x_69);
lean_dec(x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 9);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_72, x_69);
lean_dec(x_69);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_66, 2);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
lean_dec(x_74);
x_76 = 0;
x_77 = l_Lean_Name_toString(x_75, x_76);
x_78 = l_Lake_Package_pack___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lake_Package_lint___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_67);
lean_dec(x_67);
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
lean_dec(x_67);
lean_free_object(x_10);
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_66);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_88, 0, x_87);
lean_inc(x_4);
x_89 = l_Lake_Workspace_runFetchM___rarg(x_4, x_88, x_3, x_65);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_List_redLength___rarg(x_2);
x_99 = lean_mk_empty_array_with_capacity(x_98);
lean_dec(x_98);
x_100 = l_List_toArrayAux___rarg(x_2, x_99);
x_101 = l_Array_append___rarg(x_7, x_100);
lean_dec(x_100);
x_102 = l_Lake_env(x_97, x_101, x_4, x_95);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_103 = lean_ctor_get(x_93, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_104 = x_93;
} else {
 lean_dec_ref(x_93);
 x_104 = lean_box(0);
}
x_105 = l_Lake_exe___closed__4;
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_104;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_107 = lean_ctor_get(x_89, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_89, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_109 = x_89;
} else {
 lean_dec_ref(x_89);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_10);
lean_dec(x_3);
x_111 = lean_ctor_get(x_70, 0);
lean_inc(x_111);
lean_dec(x_70);
x_112 = lean_array_data(x_7);
x_113 = l_List_appendTR___rarg(x_112, x_2);
x_114 = l_Lake_Script_run(x_113, x_111, x_4, x_65);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_10, 0);
x_116 = lean_ctor_get(x_10, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 13);
lean_inc(x_120);
lean_inc(x_118);
x_121 = l_String_toName(x_118);
x_122 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_120, x_121);
lean_dec(x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 9);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_124, x_121);
lean_dec(x_121);
lean_dec(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_119);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = lean_ctor_get(x_117, 2);
lean_inc(x_126);
lean_dec(x_117);
x_127 = lean_ctor_get(x_126, 2);
lean_inc(x_127);
lean_dec(x_126);
x_128 = 0;
x_129 = l_Lean_Name_toString(x_127, x_128);
x_130 = l_Lake_Package_pack___closed__2;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lake_Package_lint___closed__2;
x_133 = lean_string_append(x_131, x_132);
x_134 = lean_string_append(x_133, x_118);
lean_dec(x_118);
x_135 = l_Lake_Package_resolveDriver___closed__6;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_116);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
x_139 = lean_ctor_get(x_125, 0);
lean_inc(x_139);
lean_dec(x_125);
if (lean_is_scalar(x_119)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_119;
}
lean_ctor_set(x_140, 0, x_117);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_141, 0, x_140);
lean_inc(x_4);
x_142 = l_Lake_Workspace_runFetchM___rarg(x_4, x_141, x_3, x_116);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_io_wait(x_145, x_144);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_List_redLength___rarg(x_2);
x_152 = lean_mk_empty_array_with_capacity(x_151);
lean_dec(x_151);
x_153 = l_List_toArrayAux___rarg(x_2, x_152);
x_154 = l_Array_append___rarg(x_7, x_153);
lean_dec(x_153);
x_155 = l_Lake_env(x_150, x_154, x_4, x_148);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
x_158 = l_Lake_exe___closed__4;
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_157;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_160 = lean_ctor_get(x_142, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_142, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_162 = x_142;
} else {
 lean_dec_ref(x_142);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_3);
x_164 = lean_ctor_get(x_122, 0);
lean_inc(x_164);
lean_dec(x_122);
x_165 = lean_array_data(x_7);
x_166 = l_List_appendTR___rarg(x_165, x_2);
x_167 = l_Lake_Script_run(x_166, x_164, x_4, x_116);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_10);
if (x_168 == 0)
{
return x_10;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_10, 0);
x_170 = lean_ctor_get(x_10, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_10);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
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
l_Lake_Package_uploadRelease___closed__8 = _init_l_Lake_Package_uploadRelease___closed__8();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__8);
l_Lake_Package_uploadRelease___closed__9 = _init_l_Lake_Package_uploadRelease___closed__9();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__9);
l_Lake_Package_uploadRelease___closed__10 = _init_l_Lake_Package_uploadRelease___closed__10();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__10);
l_Lake_Package_uploadRelease___closed__11 = _init_l_Lake_Package_uploadRelease___closed__11();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__11);
l_Lake_Package_uploadRelease___closed__12 = _init_l_Lake_Package_uploadRelease___closed__12();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__12);
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
