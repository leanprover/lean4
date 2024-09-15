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
static lean_object* l_Lake_exe___closed__5;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__10;
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
lean_object* lean_array_to_list(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_exe___lambda__1___boxed(lean_object*);
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
x_43 = lean_ctor_get(x_4, 3);
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
x_59 = lean_ctor_get(x_4, 3);
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
x_79 = lean_ctor_get(x_4, 3);
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_List_redLength___rarg(x_2);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
x_81 = l_List_toArrayAux___rarg(x_2, x_80);
x_82 = l_Array_append___rarg(x_7, x_81);
lean_dec(x_81);
x_83 = l_Lake_env(x_78, x_82, x_4, x_76);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_75);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_74, 0);
lean_dec(x_85);
x_86 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_86);
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
lean_dec(x_74);
x_88 = l_Lake_exe___closed__5;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_70);
if (x_90 == 0)
{
return x_70;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_70, 0);
x_92 = lean_ctor_get(x_70, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_70);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_23);
lean_dec(x_21);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_94 = lean_ctor_get(x_24, 0);
lean_inc(x_94);
lean_dec(x_24);
x_95 = lean_array_to_list(x_7);
x_96 = l_List_appendTR___rarg(x_95, x_2);
x_97 = l_Lake_Script_run(x_96, x_94, x_4, x_14);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_10, 1);
x_99 = lean_ctor_get(x_12, 0);
x_100 = lean_ctor_get(x_12, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_12);
x_101 = lean_ctor_get(x_99, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 2);
lean_inc(x_102);
lean_dec(x_101);
x_103 = 0;
x_104 = l_Lake_exe___closed__1;
x_105 = l_Lean_Name_toString(x_102, x_103, x_104);
x_106 = lean_ctor_get(x_99, 13);
lean_inc(x_106);
lean_inc(x_100);
x_107 = l_String_toName(x_100);
x_108 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_106, x_107);
lean_dec(x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_99, 9);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_110, x_107);
lean_dec(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_99, 8);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_113, x_107);
lean_dec(x_107);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_99);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = l_Lake_Package_pack___closed__2;
x_116 = lean_string_append(x_115, x_105);
lean_dec(x_105);
x_117 = l_Lake_Package_test___closed__2;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_100);
lean_dec(x_100);
x_120 = l_Lake_Package_resolveDriver___closed__6;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_122);
return x_10;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_100);
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_124 = x_114;
} else {
 lean_dec_ref(x_114);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_99);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = l_Lake_Package_pack___closed__2;
x_128 = lean_string_append(x_127, x_105);
lean_dec(x_105);
x_129 = l_Lake_Package_test___closed__3;
x_130 = lean_string_append(x_128, x_129);
if (lean_is_scalar(x_124)) {
 x_131 = lean_alloc_ctor(18, 1, 0);
} else {
 x_131 = x_124;
 lean_ctor_set_tag(x_131, 18);
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_131);
return x_10;
}
else
{
uint8_t x_132; 
x_132 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_3);
x_133 = l_Lake_Package_pack___closed__2;
x_134 = lean_string_append(x_133, x_105);
lean_dec(x_105);
x_135 = l_Lake_Package_test___closed__3;
x_136 = lean_string_append(x_134, x_135);
if (lean_is_scalar(x_124)) {
 x_137 = lean_alloc_ctor(18, 1, 0);
} else {
 x_137 = x_124;
 lean_ctor_set_tag(x_137, 18);
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_137);
return x_10;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_124);
lean_free_object(x_10);
x_138 = lean_box(0);
x_139 = l_Lake_Package_test___lambda__1(x_125, x_105, x_3, x_138, x_4, x_98);
lean_dec(x_105);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_100);
lean_free_object(x_10);
x_140 = lean_ctor_get(x_111, 0);
lean_inc(x_140);
lean_dec(x_111);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_99);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_142, 0, x_141);
lean_inc(x_4);
x_143 = l_Lake_Workspace_runFetchM___rarg(x_4, x_142, x_3, x_98);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_io_wait(x_146, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_List_redLength___rarg(x_2);
x_153 = lean_mk_empty_array_with_capacity(x_152);
lean_dec(x_152);
x_154 = l_List_toArrayAux___rarg(x_2, x_153);
x_155 = l_Array_append___rarg(x_7, x_154);
lean_dec(x_154);
x_156 = l_Lake_env(x_151, x_155, x_4, x_149);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_148);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_157 = lean_ctor_get(x_147, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_158 = x_147;
} else {
 lean_dec_ref(x_147);
 x_158 = lean_box(0);
}
x_159 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_158;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_161 = lean_ctor_get(x_143, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_163 = x_143;
} else {
 lean_dec_ref(x_143);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_free_object(x_10);
lean_dec(x_3);
x_165 = lean_ctor_get(x_108, 0);
lean_inc(x_165);
lean_dec(x_108);
x_166 = lean_array_to_list(x_7);
x_167 = l_List_appendTR___rarg(x_166, x_2);
x_168 = l_Lake_Script_run(x_167, x_165, x_4, x_98);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_169 = lean_ctor_get(x_10, 0);
x_170 = lean_ctor_get(x_10, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_10);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_173 = x_169;
} else {
 lean_dec_ref(x_169);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 2);
lean_inc(x_175);
lean_dec(x_174);
x_176 = 0;
x_177 = l_Lake_exe___closed__1;
x_178 = l_Lean_Name_toString(x_175, x_176, x_177);
x_179 = lean_ctor_get(x_171, 13);
lean_inc(x_179);
lean_inc(x_172);
x_180 = l_String_toName(x_172);
x_181 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_179, x_180);
lean_dec(x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_171, 9);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_183, x_180);
lean_dec(x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_171, 8);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_RBNode_find___at_Lake_Package_findLeanLib_x3f___spec__1(x_186, x_180);
lean_dec(x_180);
lean_dec(x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = l_Lake_Package_pack___closed__2;
x_189 = lean_string_append(x_188, x_178);
lean_dec(x_178);
x_190 = l_Lake_Package_test___closed__2;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_string_append(x_191, x_172);
lean_dec(x_172);
x_193 = l_Lake_Package_resolveDriver___closed__6;
x_194 = lean_string_append(x_192, x_193);
x_195 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_170);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_172);
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_198 = x_187;
} else {
 lean_dec_ref(x_187);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_173;
}
lean_ctor_set(x_199, 0, x_171);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_199);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_201 = l_Lake_Package_pack___closed__2;
x_202 = lean_string_append(x_201, x_178);
lean_dec(x_178);
x_203 = l_Lake_Package_test___closed__3;
x_204 = lean_string_append(x_202, x_203);
if (lean_is_scalar(x_198)) {
 x_205 = lean_alloc_ctor(18, 1, 0);
} else {
 x_205 = x_198;
 lean_ctor_set_tag(x_205, 18);
}
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_170);
return x_206;
}
else
{
uint8_t x_207; 
x_207 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_199);
lean_dec(x_4);
lean_dec(x_3);
x_208 = l_Lake_Package_pack___closed__2;
x_209 = lean_string_append(x_208, x_178);
lean_dec(x_178);
x_210 = l_Lake_Package_test___closed__3;
x_211 = lean_string_append(x_209, x_210);
if (lean_is_scalar(x_198)) {
 x_212 = lean_alloc_ctor(18, 1, 0);
} else {
 x_212 = x_198;
 lean_ctor_set_tag(x_212, 18);
}
lean_ctor_set(x_212, 0, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_170);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_198);
x_214 = lean_box(0);
x_215 = l_Lake_Package_test___lambda__1(x_199, x_178, x_3, x_214, x_4, x_170);
lean_dec(x_178);
return x_215;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_172);
x_216 = lean_ctor_get(x_184, 0);
lean_inc(x_216);
lean_dec(x_184);
if (lean_is_scalar(x_173)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_173;
}
lean_ctor_set(x_217, 0, x_171);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_218, 0, x_217);
lean_inc(x_4);
x_219 = l_Lake_Workspace_runFetchM___rarg(x_4, x_218, x_3, x_170);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_io_wait(x_222, x_221);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_List_redLength___rarg(x_2);
x_229 = lean_mk_empty_array_with_capacity(x_228);
lean_dec(x_228);
x_230 = l_List_toArrayAux___rarg(x_2, x_229);
x_231 = l_Array_append___rarg(x_7, x_230);
lean_dec(x_230);
x_232 = l_Lake_env(x_227, x_231, x_4, x_225);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_224);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_233 = lean_ctor_get(x_223, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_234 = x_223;
} else {
 lean_dec_ref(x_223);
 x_234 = lean_box(0);
}
x_235 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_234;
 lean_ctor_set_tag(x_236, 1);
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_237 = lean_ctor_get(x_219, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_219, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_239 = x_219;
} else {
 lean_dec_ref(x_219);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_3);
x_241 = lean_ctor_get(x_181, 0);
lean_inc(x_241);
lean_dec(x_181);
x_242 = lean_array_to_list(x_7);
x_243 = l_List_appendTR___rarg(x_242, x_2);
x_244 = l_Lake_Script_run(x_243, x_241, x_4, x_170);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = !lean_is_exclusive(x_10);
if (x_245 == 0)
{
return x_10;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_10, 0);
x_247 = lean_ctor_get(x_10, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_10);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_List_redLength___rarg(x_2);
x_48 = lean_mk_empty_array_with_capacity(x_47);
lean_dec(x_47);
x_49 = l_List_toArrayAux___rarg(x_2, x_48);
x_50 = l_Array_append___rarg(x_7, x_49);
lean_dec(x_49);
x_51 = l_Lake_env(x_46, x_50, x_4, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_42, 0);
lean_dec(x_53);
x_54 = l_Lake_exe___closed__5;
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_54);
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = l_Lake_exe___closed__5;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_38);
if (x_58 == 0)
{
return x_38;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_3);
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
lean_dec(x_19);
x_63 = lean_array_to_list(x_7);
x_64 = l_List_appendTR___rarg(x_63, x_2);
x_65 = l_Lake_Script_run(x_64, x_62, x_4, x_14);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_10, 1);
x_67 = lean_ctor_get(x_12, 0);
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_12);
x_69 = lean_ctor_get(x_67, 13);
lean_inc(x_69);
lean_inc(x_68);
x_70 = l_String_toName(x_68);
x_71 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_69, x_70);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 9);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_73, x_70);
lean_dec(x_70);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_67, 2);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
lean_dec(x_75);
x_77 = 0;
x_78 = l_Lake_exe___closed__1;
x_79 = l_Lean_Name_toString(x_76, x_77, x_78);
x_80 = l_Lake_Package_pack___closed__2;
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = l_Lake_Package_lint___closed__2;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_string_append(x_83, x_68);
lean_dec(x_68);
x_85 = l_Lake_Package_resolveDriver___closed__6;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_87);
return x_10;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_68);
lean_free_object(x_10);
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
lean_dec(x_74);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_67);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_90, 0, x_89);
lean_inc(x_4);
x_91 = l_Lake_Workspace_runFetchM___rarg(x_4, x_90, x_3, x_66);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_io_wait(x_94, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_List_redLength___rarg(x_2);
x_101 = lean_mk_empty_array_with_capacity(x_100);
lean_dec(x_100);
x_102 = l_List_toArrayAux___rarg(x_2, x_101);
x_103 = l_Array_append___rarg(x_7, x_102);
lean_dec(x_102);
x_104 = l_Lake_env(x_99, x_103, x_4, x_97);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_106 = x_95;
} else {
 lean_dec_ref(x_95);
 x_106 = lean_box(0);
}
x_107 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_106;
 lean_ctor_set_tag(x_108, 1);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_109 = lean_ctor_get(x_91, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_111 = x_91;
} else {
 lean_dec_ref(x_91);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_10);
lean_dec(x_3);
x_113 = lean_ctor_get(x_71, 0);
lean_inc(x_113);
lean_dec(x_71);
x_114 = lean_array_to_list(x_7);
x_115 = l_List_appendTR___rarg(x_114, x_2);
x_116 = l_Lake_Script_run(x_115, x_113, x_4, x_66);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_10, 0);
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_10);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_119, 13);
lean_inc(x_122);
lean_inc(x_120);
x_123 = l_String_toName(x_120);
x_124 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_122, x_123);
lean_dec(x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_119, 9);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_126, x_123);
lean_dec(x_123);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_121);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_119, 2);
lean_inc(x_128);
lean_dec(x_119);
x_129 = lean_ctor_get(x_128, 2);
lean_inc(x_129);
lean_dec(x_128);
x_130 = 0;
x_131 = l_Lake_exe___closed__1;
x_132 = l_Lean_Name_toString(x_129, x_130, x_131);
x_133 = l_Lake_Package_pack___closed__2;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Lake_Package_lint___closed__2;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_string_append(x_136, x_120);
lean_dec(x_120);
x_138 = l_Lake_Package_resolveDriver___closed__6;
x_139 = lean_string_append(x_137, x_138);
x_140 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_118);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_120);
x_142 = lean_ctor_get(x_127, 0);
lean_inc(x_142);
lean_dec(x_127);
if (lean_is_scalar(x_121)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_121;
}
lean_ctor_set(x_143, 0, x_119);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_144, 0, x_143);
lean_inc(x_4);
x_145 = l_Lake_Workspace_runFetchM___rarg(x_4, x_144, x_3, x_118);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_io_wait(x_148, x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_List_redLength___rarg(x_2);
x_155 = lean_mk_empty_array_with_capacity(x_154);
lean_dec(x_154);
x_156 = l_List_toArrayAux___rarg(x_2, x_155);
x_157 = l_Array_append___rarg(x_7, x_156);
lean_dec(x_156);
x_158 = l_Lake_env(x_153, x_157, x_4, x_151);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_150);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_160 = x_149;
} else {
 lean_dec_ref(x_149);
 x_160 = lean_box(0);
}
x_161 = l_Lake_exe___closed__5;
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_160;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_163 = lean_ctor_get(x_145, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_145, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_165 = x_145;
} else {
 lean_dec_ref(x_145);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_3);
x_167 = lean_ctor_get(x_124, 0);
lean_inc(x_167);
lean_dec(x_124);
x_168 = lean_array_to_list(x_7);
x_169 = l_List_appendTR___rarg(x_168, x_2);
x_170 = l_Lake_Script_run(x_169, x_167, x_4, x_118);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_10);
if (x_171 == 0)
{
return x_10;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_10, 0);
x_173 = lean_ctor_get(x_10, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_10);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
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
