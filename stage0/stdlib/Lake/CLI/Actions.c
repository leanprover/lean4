// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Lake.Build.Run Lake.Build.Targets Lake.Build.Common Lake.CLI.Build
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
LEAN_EXPORT lean_object* l_Lake_exe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__9;
static lean_object* l_Lake_Package_uploadRelease___closed__10;
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__0;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__1;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lake_exe___lam__0(lean_object*);
static lean_object* l_Lake_exe___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__2;
static lean_object* l_Lake_Package_test___closed__3;
static lean_object* l_Lake_exe___closed__0;
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__8;
static lean_object* l_Lake_Package_lint___closed__1;
extern lean_object* l_Lake_LeanExe_exeFacet;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__1;
static lean_object* l_Lake_exe___closed__3;
static lean_object* l_Lake_Package_uploadRelease___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed__const__1;
static lean_object* l_Lake_Package_uploadRelease___closed__11;
static lean_object* l_Lake_Package_uploadRelease___closed__4;
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__5;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
static lean_object* l_Lake_Package_uploadRelease___closed__0;
static lean_object* l_Lake_Package_test___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_resolveDriver___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object*);
static lean_object* l_Lake_Package_test___closed__4;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_lint___closed__0;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__6;
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_unpack___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0(lean_object*);
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_Package_test___closed__5;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__6;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__4;
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Package_pack___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__12;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
static lean_object* l_Lake_Package_uploadRelease___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__13;
static lean_object* l_Lake_env___closed__0;
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__0;
static lean_object* _init_l_Lake_env___closed__0() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lake_Workspace_augmentedEnvVars(x_3);
x_6 = l_Lake_env___closed__0;
x_7 = lean_box(0);
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = lean_io_process_spawn(x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_process_child_wait(x_6, x_12, x_13);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_exe___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_LeanExe_exeFacet;
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lake_LeanExe_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_12);
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
static lean_object* _init_l_Lake_exe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown executable `", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_exe___closed__2;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 1, 0);
x_8 = l_Lake_exe___closed__0;
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9, x_7);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = l_Lake_exe___closed__1;
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
x_17 = lean_alloc_closure((void*)(l_Lake_exe___lam__1), 8, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_4);
x_18 = l_Lake_Workspace_runFetchM___redArg(x_4, x_17, x_3, x_5);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_env(x_25, x_2, x_4, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_dec(x_28);
x_29 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lake_exe___closed__3;
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
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_exe___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_pack___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packing ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_pack___closed__1() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 6);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lake_Package_pack___closed__0;
x_9 = lean_string_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = l_System_FilePath_normalize(x_7);
x_14 = l_Lake_joinRelative(x_6, x_13);
lean_dec(x_13);
x_15 = 1;
x_16 = l_Lake_Package_pack___closed__1;
x_17 = l_Lake_tar(x_14, x_2, x_15, x_16, x_12, x_4);
return x_17;
}
}
static lean_object* _init_l_Lake_Package_unpack___closed__0() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 6);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lake_Package_unpack___closed__0;
x_9 = lean_string_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = l_System_FilePath_normalize(x_7);
x_14 = l_Lake_joinRelative(x_6, x_13);
lean_dec(x_13);
x_15 = 1;
x_16 = l_Lake_untar(x_2, x_14, x_15, x_12, x_4);
return x_16;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gh", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uploading ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--clobber", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__5;
x_2 = l_Lake_Package_uploadRelease___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__6;
x_2 = l_Lake_Package_uploadRelease___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_uploadRelease___closed__11;
x_2 = l_Lake_Package_uploadRelease___closed__12;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 16);
lean_inc(x_19);
x_20 = l_Lake_Package_uploadRelease___closed__2;
x_21 = l_Lake_joinRelative(x_17, x_20);
x_22 = l_Lake_joinRelative(x_21, x_19);
lean_inc(x_22);
x_23 = l_Lake_Package_pack(x_1, x_22, x_3, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_18, 11);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lake_Package_uploadRelease___closed__3;
x_29 = lean_string_append(x_28, x_2);
x_30 = l_Lake_Package_uploadRelease___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_19);
lean_dec(x_19);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_push(x_26, x_34);
x_36 = l_Lake_Package_uploadRelease___closed__7;
x_37 = l_Lake_Package_uploadRelease___closed__10;
x_38 = lean_array_push(x_37, x_2);
x_39 = lean_array_push(x_38, x_22);
x_40 = lean_array_push(x_39, x_36);
if (lean_obj_tag(x_27) == 0)
{
x_5 = x_40;
x_6 = x_35;
x_7 = x_25;
goto block_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = l_Lake_Package_uploadRelease___closed__13;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Array_append___redArg(x_40, x_43);
lean_dec(x_43);
x_5 = x_44;
x_6 = x_35;
x_7 = x_25;
goto block_16;
}
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
return x_23;
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lake_env___closed__0;
x_9 = l_Lake_Package_uploadRelease___closed__0;
x_10 = lean_box(0);
x_11 = l_Lake_Package_uploadRelease___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_proc(x_14, x_13, x_6, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_17 = l_List_reverse___redArg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_resolveDriver___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" driver '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (too many '/')", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": unknown ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" driver package '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_resolveDriver___closed__7() {
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_Package_resolveDriver___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Name_toString(x_6, x_7, x_9);
x_23 = lean_string_utf8_byte_size(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_1);
x_11 = x_5;
goto block_22;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_dec(x_30);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
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
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_43 = l_String_toName(x_37);
x_44 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_42, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
lean_free_object(x_26);
x_45 = l_Lake_Package_resolveDriver___closed__3;
x_46 = lean_string_append(x_10, x_45);
x_47 = lean_string_append(x_46, x_2);
x_48 = l_Lake_Package_resolveDriver___closed__4;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_37);
lean_dec(x_37);
x_51 = l_Lake_Package_resolveDriver___closed__5;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_53);
return x_27;
}
else
{
lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_10);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_40);
lean_ctor_set(x_27, 0, x_54);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_27);
return x_26;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
lean_dec(x_27);
x_56 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_57 = l_String_toName(x_37);
x_58 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_56, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
lean_free_object(x_26);
x_59 = l_Lake_Package_resolveDriver___closed__3;
x_60 = lean_string_append(x_10, x_59);
x_61 = lean_string_append(x_60, x_2);
x_62 = l_Lake_Package_resolveDriver___closed__4;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_37);
lean_dec(x_37);
x_65 = l_Lake_Package_resolveDriver___closed__5;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_37);
lean_dec(x_10);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
lean_dec(x_58);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_70);
return x_26;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_26, 0);
lean_inc(x_71);
lean_dec(x_26);
x_72 = lean_ctor_get(x_27, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_73 = x_27;
} else {
 lean_dec_ref(x_27);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_4, 4);
lean_inc(x_71);
x_75 = l_String_toName(x_71);
x_76 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_74, x_75);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_72);
x_77 = l_Lake_Package_resolveDriver___closed__3;
x_78 = lean_string_append(x_10, x_77);
x_79 = lean_string_append(x_78, x_2);
x_80 = l_Lake_Package_resolveDriver___closed__4;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_71);
lean_dec(x_71);
x_83 = l_Lake_Package_resolveDriver___closed__5;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_5);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_10);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
if (lean_is_scalar(x_73)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_73;
 lean_ctor_set_tag(x_88, 0);
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_72);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
return x_89;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_26);
x_11 = x_5;
goto block_22;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_90 = l_Lake_Package_resolveDriver___closed__6;
x_91 = lean_string_append(x_10, x_90);
x_92 = lean_string_append(x_91, x_2);
x_93 = l_Lake_Package_resolveDriver___closed__7;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l_Lake_Package_resolveDriver___closed__0;
x_13 = lean_string_append(x_10, x_12);
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lake_Package_resolveDriver___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_3);
x_18 = l_Lake_Package_resolveDriver___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_Package_resolveDriver___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lake_LeanExe_exeFacet;
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_apply_7(x_5, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_Lake_Package_test___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_Package_resolveDriver___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_test___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": arguments cannot be passed to a library test driver", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid test driver: unknown script, executable, or library '", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_test___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_test___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid test driver: ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 17);
lean_inc(x_7);
x_8 = l_Lake_Package_test___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_15 = x_10;
} else {
 lean_dec_ref(x_10);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_6, 14);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 13);
lean_inc(x_18);
lean_inc(x_14);
x_19 = l_String_toName(x_14);
x_20 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_119; 
x_21 = 0;
x_22 = l_Lake_Package_test___closed__1;
lean_inc(x_17);
x_23 = l_Lean_Name_toString(x_17, x_21, x_22);
x_119 = l_Lake_Package_findTargetDecl_x3f(x_19, x_11);
if (lean_obj_tag(x_119) == 0)
{
lean_dec(x_17);
goto block_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 3);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lake_LeanExe_keyword;
x_125 = lean_name_eq(x_122, x_124);
lean_dec(x_122);
if (x_125 == 0)
{
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_17);
goto block_118;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_121);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_11);
lean_ctor_set(x_126, 1, x_121);
lean_ctor_set(x_126, 2, x_123);
x_127 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1), 11, 4);
lean_closure_set(x_127, 0, x_17);
lean_closure_set(x_127, 1, x_121);
lean_closure_set(x_127, 2, x_124);
lean_closure_set(x_127, 3, x_126);
lean_inc(x_4);
x_128 = l_Lake_Workspace_runFetchM___redArg(x_4, x_127, x_3, x_12);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_io_wait(x_131, x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_array_mk(x_2);
x_137 = l_Array_append___redArg(x_16, x_136);
lean_dec(x_136);
x_138 = l_Lake_env(x_135, x_137, x_4, x_134);
return x_138;
}
else
{
uint8_t x_139; 
lean_dec(x_133);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_132);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_132, 0);
lean_dec(x_140);
x_141 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 0, x_141);
return x_132;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_dec(x_132);
x_143 = l_Lake_exe___closed__3;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_128);
if (x_145 == 0)
{
return x_128;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_128, 0);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_128);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lake_Package_test___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_13)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_13;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
block_36:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lake_Package_test___closed__3;
x_30 = lean_string_append(x_23, x_29);
x_31 = lean_string_append(x_30, x_14);
lean_dec(x_14);
x_32 = l_Lake_Package_resolveDriver___closed__5;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_15)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_15;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
return x_35;
}
block_118:
{
lean_object* x_37; 
x_37 = l_Lake_Package_findTargetDecl_x3f(x_19, x_11);
lean_dec(x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lake_Package_test___closed__5;
x_43 = lean_name_eq(x_40, x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_36;
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_14);
x_44 = l_Array_isEmpty___redArg(x_16);
lean_dec(x_16);
if (x_44 == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_28;
}
else
{
uint8_t x_45; 
x_45 = l_List_isEmpty___redArg(x_2);
lean_dec(x_2);
if (x_45 == 0)
{
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
goto block_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_41);
x_47 = lean_box(0);
x_48 = l_Lake_resolveLibTarget(x_4, x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lake_Package_test___closed__6;
x_52 = lean_string_append(x_23, x_51);
x_53 = l_Lake_CliError_toString(x_50);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
lean_ctor_set_tag(x_48, 18);
lean_ctor_set(x_48, 0, x_54);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_12);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = l_Lake_Package_test___closed__6;
x_58 = lean_string_append(x_23, x_57);
x_59 = l_Lake_CliError_toString(x_56);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_12);
return x_62;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_23);
x_63 = lean_ctor_get(x_48, 0);
lean_inc(x_63);
lean_dec(x_48);
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_3, 0);
lean_dec(x_65);
x_66 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_66, 0, x_63);
x_67 = lean_box(0);
lean_ctor_set(x_3, 0, x_67);
x_68 = l_Lake_Workspace_runFetchM___redArg(x_4, x_66, x_3, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_io_wait(x_71, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = l_Lake_Package_test___boxed__const__1;
lean_ctor_set(x_72, 0, x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = l_Lake_Package_test___boxed__const__1;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_73);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_72, 0);
lean_dec(x_81);
x_82 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_82);
return x_72;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = l_Lake_exe___closed__3;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_68);
if (x_86 == 0)
{
return x_68;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_68, 0);
x_88 = lean_ctor_get(x_68, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_68);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_91 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_92 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_93 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_95 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_96 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_dec(x_3);
x_97 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_97, 0, x_63);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_90);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 1, x_91);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 2, x_92);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 3, x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 4, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 5, x_95);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 6, x_96);
x_100 = l_Lake_Workspace_runFetchM___redArg(x_4, x_97, x_99, x_12);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_io_wait(x_103, x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = l_Lake_Package_test___boxed__const__1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_105);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
 x_111 = lean_box(0);
}
x_112 = l_Lake_exe___closed__3;
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_111;
 lean_ctor_set_tag(x_113, 1);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_100, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_116 = x_100;
} else {
 lean_dec_ref(x_100);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
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
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_149 = lean_ctor_get(x_20, 0);
lean_inc(x_149);
lean_dec(x_20);
x_150 = lean_array_to_list(x_16);
x_151 = l_List_appendTR___redArg(x_150, x_2);
x_152 = l_Lake_Script_run(x_151, x_149, x_4, x_12);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_9);
if (x_153 == 0)
{
return x_9;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_9, 0);
x_155 = lean_ctor_get(x_9, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_9);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
static lean_object* _init_l_Lake_Package_lint___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lint", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_lint___closed__1() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 18);
lean_inc(x_7);
x_8 = l_Lake_Package_lint___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_6, 16);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 13);
lean_inc(x_17);
lean_inc(x_14);
x_29 = l_String_toName(x_14);
x_30 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_17, x_29);
lean_dec(x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = l_Lake_Package_findTargetDecl_x3f(x_29, x_11);
lean_dec(x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lake_LeanExe_keyword;
x_37 = lean_name_eq(x_34, x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_33);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1), 11, 4);
lean_closure_set(x_39, 0, x_16);
lean_closure_set(x_39, 1, x_33);
lean_closure_set(x_39, 2, x_36);
lean_closure_set(x_39, 3, x_38);
lean_inc(x_4);
x_40 = l_Lake_Workspace_runFetchM___redArg(x_4, x_39, x_3, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_io_wait(x_43, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_mk(x_2);
x_49 = l_Array_append___redArg(x_15, x_48);
lean_dec(x_48);
x_50 = l_Lake_env(x_47, x_49, x_4, x_46);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_44, 0);
lean_dec(x_52);
x_53 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = l_Lake_exe___closed__3;
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
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_40, 0);
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_40);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_61 = lean_ctor_get(x_30, 0);
lean_inc(x_61);
lean_dec(x_30);
x_62 = lean_array_to_list(x_15);
x_63 = l_List_appendTR___redArg(x_62, x_2);
x_64 = l_Lake_Script_run(x_63, x_61, x_4, x_12);
return x_64;
}
block_28:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = 0;
x_19 = l_Lake_Package_test___closed__1;
x_20 = l_Lean_Name_toString(x_16, x_18, x_19);
x_21 = l_Lake_Package_lint___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_14);
lean_dec(x_14);
x_24 = l_Lake_Package_resolveDriver___closed__5;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_13)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_13;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Run(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_env___closed__0 = _init_l_Lake_env___closed__0();
lean_mark_persistent(l_Lake_env___closed__0);
l_Lake_exe___closed__0 = _init_l_Lake_exe___closed__0();
lean_mark_persistent(l_Lake_exe___closed__0);
l_Lake_exe___closed__1 = _init_l_Lake_exe___closed__1();
lean_mark_persistent(l_Lake_exe___closed__1);
l_Lake_exe___closed__2 = _init_l_Lake_exe___closed__2();
lean_mark_persistent(l_Lake_exe___closed__2);
l_Lake_exe___closed__3 = _init_l_Lake_exe___closed__3();
lean_mark_persistent(l_Lake_exe___closed__3);
l_Lake_Package_pack___closed__0 = _init_l_Lake_Package_pack___closed__0();
lean_mark_persistent(l_Lake_Package_pack___closed__0);
l_Lake_Package_pack___closed__1 = _init_l_Lake_Package_pack___closed__1();
lean_mark_persistent(l_Lake_Package_pack___closed__1);
l_Lake_Package_unpack___closed__0 = _init_l_Lake_Package_unpack___closed__0();
lean_mark_persistent(l_Lake_Package_unpack___closed__0);
l_Lake_Package_uploadRelease___closed__0 = _init_l_Lake_Package_uploadRelease___closed__0();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__0);
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
l_Lake_Package_uploadRelease___closed__13 = _init_l_Lake_Package_uploadRelease___closed__13();
lean_mark_persistent(l_Lake_Package_uploadRelease___closed__13);
l_Lake_Package_resolveDriver___closed__0 = _init_l_Lake_Package_resolveDriver___closed__0();
lean_mark_persistent(l_Lake_Package_resolveDriver___closed__0);
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
l_Lake_Package_test___closed__0 = _init_l_Lake_Package_test___closed__0();
lean_mark_persistent(l_Lake_Package_test___closed__0);
l_Lake_Package_test___closed__1 = _init_l_Lake_Package_test___closed__1();
lean_mark_persistent(l_Lake_Package_test___closed__1);
l_Lake_Package_test___closed__2 = _init_l_Lake_Package_test___closed__2();
lean_mark_persistent(l_Lake_Package_test___closed__2);
l_Lake_Package_test___closed__3 = _init_l_Lake_Package_test___closed__3();
lean_mark_persistent(l_Lake_Package_test___closed__3);
l_Lake_Package_test___closed__4 = _init_l_Lake_Package_test___closed__4();
lean_mark_persistent(l_Lake_Package_test___closed__4);
l_Lake_Package_test___closed__5 = _init_l_Lake_Package_test___closed__5();
lean_mark_persistent(l_Lake_Package_test___closed__5);
l_Lake_Package_test___closed__6 = _init_l_Lake_Package_test___closed__6();
lean_mark_persistent(l_Lake_Package_test___closed__6);
l_Lake_Package_test___boxed__const__1 = _init_l_Lake_Package_test___boxed__const__1();
lean_mark_persistent(l_Lake_Package_test___boxed__const__1);
l_Lake_Package_lint___closed__0 = _init_l_Lake_Package_lint___closed__0();
lean_mark_persistent(l_Lake_Package_lint___closed__0);
l_Lake_Package_lint___closed__1 = _init_l_Lake_Package_lint___closed__1();
lean_mark_persistent(l_Lake_Package_lint___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
