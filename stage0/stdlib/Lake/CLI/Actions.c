// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Lake.Build.Run Lake.Build.Targets Lake.Build.Module Lake.CLI.Build
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
static lean_object* l_Lake_Package_uploadRelease___closed__10;
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__1;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
static lean_object* l_Lake_Package_test___closed__4;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_lint___closed__0;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_unpack___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__12;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
static lean_object* l_Lake_Package_uploadRelease___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__13;
static lean_object* l_Lake_env___closed__0;
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__0;
lean_object* l_Lake_prepareLeanCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(x_11);
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
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = l_Lake_exe___closed__0;
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = l_Lake_exe___closed__1;
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
lean_dec_ref(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_exe___lam__0), 8, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_4);
x_17 = l_Lake_Workspace_runFetchM___redArg(x_4, x_16, x_3, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_io_wait(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lake_env(x_24, x_2, x_4, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_22);
lean_dec(x_4);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lake_exe___closed__3;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 6);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_Lake_Package_pack___closed__0;
x_9 = lean_string_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = l_System_FilePath_normalize(x_7);
x_14 = l_Lake_joinRelative(x_6, x_13);
lean_dec_ref(x_13);
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 6);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_Lake_Package_unpack___closed__0;
x_9 = lean_string_append(x_8, x_2);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = l_System_FilePath_normalize(x_7);
x_14 = l_Lake_joinRelative(x_6, x_13);
lean_dec_ref(x_13);
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
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_19);
x_20 = l_Lake_Package_uploadRelease___closed__2;
x_21 = l_Lake_joinRelative(x_17, x_20);
x_22 = l_Lake_joinRelative(x_21, x_19);
lean_inc_ref(x_22);
x_23 = l_Lake_Package_pack(x_1, x_22, x_3, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_18, 11);
lean_inc(x_27);
lean_dec_ref(x_18);
x_28 = l_Lake_Package_uploadRelease___closed__3;
x_29 = lean_string_append(x_28, x_2);
x_30 = l_Lake_Package_uploadRelease___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_19);
lean_dec_ref(x_19);
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
lean_dec_ref(x_27);
x_42 = l_Lake_Package_uploadRelease___closed__13;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Array_append___redArg(x_40, x_43);
lean_dec_ref(x_43);
x_5 = x_44;
x_6 = x_35;
x_7 = x_25;
goto block_16;
}
}
else
{
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = 0;
x_8 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_6, x_7);
x_21 = lean_string_utf8_byte_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_1);
x_9 = x_5;
goto block_20;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec_ref(x_8);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_dec(x_28);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_27);
lean_ctor_set(x_24, 0, x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_4, 4);
lean_inc(x_35);
x_41 = l_String_toName(x_35);
x_42 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_40, x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_free_object(x_24);
x_43 = l_Lake_Package_resolveDriver___closed__3;
x_44 = lean_string_append(x_8, x_43);
x_45 = lean_string_append(x_44, x_2);
x_46 = l_Lake_Package_resolveDriver___closed__4;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_string_append(x_47, x_35);
lean_dec(x_35);
x_49 = l_Lake_Package_resolveDriver___closed__5;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 0, x_51);
return x_25;
}
else
{
lean_object* x_52; 
lean_dec(x_35);
lean_dec_ref(x_8);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec_ref(x_42);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 1, x_38);
lean_ctor_set(x_25, 0, x_52);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 0, x_25);
return x_24;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_25, 0);
lean_inc(x_53);
lean_dec(x_25);
x_54 = lean_ctor_get(x_4, 4);
lean_inc(x_35);
x_55 = l_String_toName(x_35);
x_56 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_54, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
lean_free_object(x_24);
x_57 = l_Lake_Package_resolveDriver___closed__3;
x_58 = lean_string_append(x_8, x_57);
x_59 = lean_string_append(x_58, x_2);
x_60 = l_Lake_Package_resolveDriver___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_35);
lean_dec(x_35);
x_63 = l_Lake_Package_resolveDriver___closed__5;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_5);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_35);
lean_dec_ref(x_8);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec_ref(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_53);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 0, x_68);
return x_24;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_24, 0);
lean_inc(x_69);
lean_dec(x_24);
x_70 = lean_ctor_get(x_25, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_71 = x_25;
} else {
 lean_dec_ref(x_25);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_4, 4);
lean_inc(x_69);
x_73 = l_String_toName(x_69);
x_74 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_72, x_73);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_70);
x_75 = l_Lake_Package_resolveDriver___closed__3;
x_76 = lean_string_append(x_8, x_75);
x_77 = lean_string_append(x_76, x_2);
x_78 = l_Lake_Package_resolveDriver___closed__4;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_string_append(x_79, x_69);
lean_dec(x_69);
x_81 = l_Lake_Package_resolveDriver___closed__5;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_5);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_69);
lean_dec_ref(x_8);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec_ref(x_74);
if (lean_is_scalar(x_71)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_71;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_70);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_5);
return x_87;
}
}
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_9 = x_5;
goto block_20;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_1);
x_88 = l_Lake_Package_resolveDriver___closed__6;
x_89 = lean_string_append(x_8, x_88);
x_90 = lean_string_append(x_89, x_2);
x_91 = l_Lake_Package_resolveDriver___closed__7;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_5);
return x_94;
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lake_Package_resolveDriver___closed__0;
x_11 = lean_string_append(x_8, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_Package_resolveDriver___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_3);
x_16 = l_Lake_Package_resolveDriver___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_resolveDriver(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": arguments cannot be passed to a library test driver", 53, 53);
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
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_test___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_test___closed__5() {
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
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 17);
lean_inc_ref(x_7);
x_8 = l_Lake_Package_test___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4, x_5);
lean_dec_ref(x_7);
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
lean_inc_ref(x_16);
lean_dec_ref(x_6);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 13);
lean_inc(x_18);
lean_inc(x_14);
x_19 = l_String_toName(x_14);
x_20 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_119; 
x_21 = 0;
lean_inc(x_17);
x_22 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_17, x_21);
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
lean_dec_ref(x_119);
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
lean_dec_ref(x_22);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_121);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_11);
lean_ctor_set(x_126, 1, x_121);
lean_ctor_set(x_126, 2, x_123);
x_127 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0), 11, 4);
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
lean_dec_ref(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_131);
lean_dec(x_129);
x_132 = lean_io_wait(x_131, x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_array_mk(x_2);
x_137 = l_Array_append___redArg(x_16, x_136);
lean_dec_ref(x_136);
x_138 = l_Lake_env(x_135, x_137, x_4, x_134);
return x_138;
}
else
{
uint8_t x_139; 
lean_dec_ref(x_133);
lean_dec_ref(x_16);
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
lean_dec_ref(x_16);
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
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lake_Package_test___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_13)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_13;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lake_Package_test___closed__2;
x_29 = lean_string_append(x_22, x_28);
x_30 = lean_string_append(x_29, x_14);
lean_dec(x_14);
x_31 = l_Lake_Package_resolveDriver___closed__5;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_15)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_15;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_12);
return x_34;
}
block_118:
{
lean_object* x_36; 
x_36 = l_Lake_Package_findTargetDecl_x3f(x_19, x_11);
lean_dec(x_19);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 3);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lake_Package_test___closed__4;
x_42 = lean_name_eq(x_39, x_41);
lean_dec(x_39);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_35;
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_14);
x_43 = l_Array_isEmpty___redArg(x_16);
lean_dec_ref(x_16);
if (x_43 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_27;
}
else
{
uint8_t x_44; 
x_44 = l_List_isEmpty___redArg(x_2);
lean_dec(x_2);
if (x_44 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_13);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_40);
x_46 = lean_box(0);
x_47 = l_Lake_resolveLibTarget(x_4, x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lake_Package_test___closed__5;
x_51 = lean_string_append(x_22, x_50);
x_52 = l_Lake_CliError_toString(x_49);
x_53 = lean_string_append(x_51, x_52);
lean_dec_ref(x_52);
lean_ctor_set_tag(x_47, 18);
lean_ctor_set(x_47, 0, x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_12);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Lake_Package_test___closed__5;
x_57 = lean_string_append(x_22, x_56);
x_58 = l_Lake_CliError_toString(x_55);
x_59 = lean_string_append(x_57, x_58);
lean_dec_ref(x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_12);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec_ref(x_22);
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec_ref(x_47);
x_63 = !lean_is_exclusive(x_3);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_3, 0);
lean_dec(x_64);
x_65 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_65, 0, x_62);
x_66 = lean_box(0);
lean_ctor_set(x_3, 0, x_66);
x_67 = l_Lake_Workspace_runFetchM___redArg(x_4, x_65, x_3, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_70);
lean_dec(x_68);
x_71 = lean_io_wait(x_70, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec_ref(x_72);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
x_75 = l_Lake_Package_test___boxed__const__1;
lean_ctor_set(x_71, 0, x_75);
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_dec(x_71);
x_77 = l_Lake_Package_test___boxed__const__1;
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_72);
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_71, 0);
lean_dec(x_80);
x_81 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_81);
return x_71;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_dec(x_71);
x_83 = l_Lake_exe___closed__3;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_67);
if (x_85 == 0)
{
return x_67;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_67, 0);
x_87 = lean_ctor_get(x_67, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_67);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_90 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_91 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_92 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_93 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_95 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_96 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 7);
lean_dec(x_3);
x_97 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_97, 0, x_62);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_89);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 1, x_90);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 2, x_91);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 3, x_92);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 4, x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 5, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 6, x_95);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 7, x_96);
x_100 = l_Lake_Workspace_runFetchM___redArg(x_4, x_97, x_99, x_12);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_103);
lean_dec(x_101);
x_104 = lean_io_wait(x_103, x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_105);
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
lean_dec_ref(x_105);
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
lean_dec_ref(x_3);
x_149 = lean_ctor_get(x_20, 0);
lean_inc(x_149);
lean_dec_ref(x_20);
x_150 = lean_array_to_list(x_16);
x_151 = l_List_appendTR___redArg(x_150, x_2);
x_152 = l_Lake_Script_run(x_151, x_149, x_4, x_12);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_7);
x_8 = l_Lake_Package_lint___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4, x_5);
lean_dec_ref(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; 
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
lean_inc_ref(x_15);
lean_dec_ref(x_6);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 13);
lean_inc(x_17);
lean_inc(x_14);
x_28 = l_String_toName(x_14);
x_29 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_28);
lean_dec(x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = l_Lake_Package_findTargetDecl_x3f(x_28, x_11);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 3);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lake_LeanExe_keyword;
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_32);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_34);
x_38 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0), 11, 4);
lean_closure_set(x_38, 0, x_16);
lean_closure_set(x_38, 1, x_32);
lean_closure_set(x_38, 2, x_35);
lean_closure_set(x_38, 3, x_37);
lean_inc(x_4);
x_39 = l_Lake_Workspace_runFetchM___redArg(x_4, x_38, x_3, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec(x_40);
x_43 = lean_io_wait(x_42, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_array_mk(x_2);
x_48 = l_Array_append___redArg(x_15, x_47);
lean_dec_ref(x_47);
x_49 = l_Lake_env(x_46, x_48, x_4, x_45);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec_ref(x_44);
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_52 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = l_Lake_exe___closed__3;
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
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_3);
x_60 = lean_ctor_get(x_29, 0);
lean_inc(x_60);
lean_dec_ref(x_29);
x_61 = lean_array_to_list(x_15);
x_62 = l_List_appendTR___redArg(x_61, x_2);
x_63 = l_Lake_Script_run(x_62, x_60, x_4, x_12);
return x_63;
}
block_27:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = 0;
x_19 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_16, x_18);
x_20 = l_Lake_Package_lint___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_14);
lean_dec(x_14);
x_23 = l_Lake_Package_resolveDriver___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_13)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_13;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_9);
if (x_64 == 0)
{
return x_9;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_9, 0);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_9);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand), 9, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lake_Workspace_runFetchM___redArg(x_1, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_io_wait(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_14);
x_15 = lean_io_process_spawn(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_18);
lean_dec(x_14);
x_19 = lean_io_process_child_wait(x_18, x_16, x_17);
lean_dec(x_16);
lean_dec_ref(x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_12);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_26 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l_Lake_exe___closed__3;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
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
res = initialize_Lake_Build_Module(builtin, lean_io_mk_world());
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
