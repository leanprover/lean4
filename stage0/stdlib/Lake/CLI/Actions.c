// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: public import Lake.Config.Workspace import Lake.Build.Run import Lake.Build.Actions import Lake.Build.Targets import Lake.Build.Module import Lake.CLI.Build import Lake.Util.Proc
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
static lean_object* l_Lake_Package_resolveDriver___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__9;
static lean_object* l_Lake_Package_uploadRelease___closed__10;
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__0;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__1;
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_Package_resolveDriver_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__8;
static lean_object* l_Lake_Package_lint___closed__1;
extern lean_object* l_Lake_LeanExe_exeFacet;
static lean_object* l_Lake_exe___closed__1;
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__3;
static lean_object* l_Lake_Package_uploadRelease___closed__5;
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed__const__1;
static lean_object* l_Lake_Package_uploadRelease___closed__11;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__5;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
static lean_object* l_Lake_Package_test___closed__4;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_lint___closed__0;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_unpack___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_Package_test___closed__5;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__6;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__4;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lake_LeanExe_exeFacet;
lean_inc(x_10);
lean_inc(x_11);
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
x_2 = lean_mk_io_user_error(x_1);
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
x_13 = lean_mk_io_user_error(x_12);
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_io_wait(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lake_env(x_25, x_2, x_4, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_23);
lean_dec(x_4);
lean_dec_ref(x_2);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_31);
lean_dec(x_29);
x_32 = lean_io_wait(x_31, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lake_env(x_35, x_2, x_4, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_33);
lean_dec(x_4);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec_ref(x_32);
x_38 = l_Lake_exe___closed__3;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
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
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
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
x_1 = l_Lake_defaultLakeDir;
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
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 17);
lean_inc_ref(x_19);
x_20 = l_Lake_Package_uploadRelease___closed__2;
lean_inc_ref(x_17);
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
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_Package_resolveDriver_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_3, x_4);
return x_5;
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
x_7 = 0;
lean_inc(x_6);
x_8 = l_Lean_Name_toString(x_6, x_7);
x_21 = lean_string_utf8_byte_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_String_splitAux___at___Lake_Package_resolveDriver_spec__0(x_3, x_22, x_22, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_1);
x_9 = x_5;
goto block_20;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec_ref(x_8);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_dec(x_29);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 1, x_28);
lean_ctor_set(x_25, 0, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec_ref(x_1);
x_34 = lean_ctor_get(x_26, 1);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_4, 5);
lean_inc(x_36);
x_42 = l_String_toName(x_36);
x_43 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_41, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
lean_free_object(x_25);
x_44 = l_Lake_Package_resolveDriver___closed__3;
x_45 = lean_string_append(x_8, x_44);
x_46 = lean_string_append(x_45, x_2);
x_47 = l_Lake_Package_resolveDriver___closed__4;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_36);
lean_dec(x_36);
x_50 = l_Lake_Package_resolveDriver___closed__5;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_mk_io_user_error(x_51);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_52);
return x_26;
}
else
{
lean_object* x_53; 
lean_dec(x_36);
lean_dec_ref(x_8);
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec_ref(x_43);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_39);
lean_ctor_set(x_26, 0, x_53);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 0, x_26);
return x_25;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
lean_dec(x_26);
x_55 = lean_ctor_get(x_4, 5);
lean_inc(x_36);
x_56 = l_String_toName(x_36);
x_57 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_55, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_54);
lean_free_object(x_25);
x_58 = l_Lake_Package_resolveDriver___closed__3;
x_59 = lean_string_append(x_8, x_58);
x_60 = lean_string_append(x_59, x_2);
x_61 = l_Lake_Package_resolveDriver___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_36);
lean_dec(x_36);
x_64 = l_Lake_Package_resolveDriver___closed__5;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_mk_io_user_error(x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_36);
lean_dec_ref(x_8);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec_ref(x_57);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_54);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 0, x_69);
return x_25;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_25, 0);
lean_inc(x_70);
lean_dec(x_25);
x_71 = lean_ctor_get(x_26, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_72 = x_26;
} else {
 lean_dec_ref(x_26);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_4, 5);
lean_inc(x_70);
x_74 = l_String_toName(x_70);
x_75 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_73, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
x_76 = l_Lake_Package_resolveDriver___closed__3;
x_77 = lean_string_append(x_8, x_76);
x_78 = lean_string_append(x_77, x_2);
x_79 = l_Lake_Package_resolveDriver___closed__4;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_70);
lean_dec(x_70);
x_82 = l_Lake_Package_resolveDriver___closed__5;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_mk_io_user_error(x_83);
if (lean_is_scalar(x_72)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_72;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_5);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_70);
lean_dec_ref(x_8);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec_ref(x_75);
if (lean_is_scalar(x_72)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_72;
 lean_ctor_set_tag(x_87, 0);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_71);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_5);
return x_88;
}
}
}
else
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_9 = x_5;
goto block_20;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_1);
x_89 = l_Lake_Package_resolveDriver___closed__6;
x_90 = lean_string_append(x_8, x_89);
x_91 = lean_string_append(x_90, x_2);
x_92 = l_Lake_Package_resolveDriver___closed__7;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_mk_io_user_error(x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
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
x_18 = lean_mk_io_user_error(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___Lake_Package_resolveDriver_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
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
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 18);
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
x_18 = lean_ctor_get(x_11, 14);
lean_inc(x_14);
x_19 = l_String_toName(x_14);
x_20 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_144; 
x_21 = 0;
lean_inc(x_17);
x_22 = l_Lean_Name_toString(x_17, x_21);
x_144 = l_Lake_Package_findTargetDecl_x3f(x_19, x_11);
if (lean_obj_tag(x_144) == 0)
{
goto block_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 3);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l_Lake_LeanExe_keyword;
x_150 = lean_name_eq(x_147, x_149);
lean_dec(x_147);
if (x_150 == 0)
{
lean_dec(x_148);
lean_dec(x_146);
goto block_143;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_22);
lean_dec(x_19);
lean_inc(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_146);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_11);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_148);
x_152 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0), 11, 4);
lean_closure_set(x_152, 0, x_17);
lean_closure_set(x_152, 1, x_146);
lean_closure_set(x_152, 2, x_149);
lean_closure_set(x_152, 3, x_151);
lean_inc(x_4);
x_153 = l_Lake_Workspace_runFetchM___redArg(x_4, x_152, x_3, x_12);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
x_157 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_157);
lean_dec(x_155);
x_158 = lean_io_wait(x_157, x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_free_object(x_153);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_array_mk(x_2);
x_163 = l_Array_append___redArg(x_16, x_162);
lean_dec_ref(x_162);
x_164 = l_Lake_env(x_161, x_163, x_4, x_160);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_159);
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
lean_dec_ref(x_158);
x_166 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 1, x_165);
lean_ctor_set(x_153, 0, x_166);
return x_153;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_153, 0);
x_168 = lean_ctor_get(x_153, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_153);
x_169 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_169);
lean_dec(x_167);
x_170 = lean_io_wait(x_169, x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = lean_array_mk(x_2);
x_175 = l_Array_append___redArg(x_16, x_174);
lean_dec_ref(x_174);
x_176 = l_Lake_env(x_173, x_175, x_4, x_172);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_171);
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_dec_ref(x_170);
x_178 = l_Lake_exe___closed__3;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_153);
if (x_180 == 0)
{
return x_153;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_153, 0);
x_182 = lean_ctor_get(x_153, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_153);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lake_Package_test___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_mk_io_user_error(x_24);
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
x_33 = lean_mk_io_user_error(x_32);
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
block_143:
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lake_Package_test___closed__5;
x_50 = lean_string_append(x_22, x_49);
x_51 = l_Lake_CliError_toString(x_48);
x_52 = lean_string_append(x_50, x_51);
lean_dec_ref(x_51);
x_53 = lean_mk_io_user_error(x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_12);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_22);
x_55 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
lean_dec_ref(x_47);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_3, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_dec(x_60);
x_61 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_61, 0, x_56);
x_62 = lean_box(0);
lean_ctor_set(x_55, 0, x_62);
x_63 = l_Lake_Workspace_runFetchM___redArg(x_4, x_61, x_3, x_12);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
lean_dec(x_65);
x_68 = lean_io_wait(x_67, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Lake_Package_test___boxed__const__1;
lean_ctor_set(x_63, 1, x_70);
lean_ctor_set(x_63, 0, x_71);
return x_63;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec_ref(x_68);
x_73 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 1, x_72);
lean_ctor_set(x_63, 0, x_73);
return x_63;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_76);
lean_dec(x_74);
x_77 = lean_io_wait(x_76, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = l_Lake_Package_test___boxed__const__1;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_78);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec_ref(x_77);
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
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
return x_63;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
x_90 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 1);
x_91 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 2);
lean_dec(x_55);
x_92 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_92, 0, x_56);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_89);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_90);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 2, x_91);
lean_ctor_set(x_3, 0, x_94);
x_95 = l_Lake_Workspace_runFetchM___redArg(x_4, x_92, x_3, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_99);
lean_dec(x_96);
x_100 = lean_io_wait(x_99, x_97);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = l_Lake_Package_test___boxed__const__1;
if (lean_is_scalar(x_98)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_98;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_101);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_dec_ref(x_100);
x_106 = l_Lake_exe___closed__3;
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_110 = x_95;
} else {
 lean_dec_ref(x_95);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_112 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_113 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_114 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_115 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_116 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_117 = lean_ctor_get(x_3, 1);
lean_inc(x_117);
lean_dec(x_3);
x_118 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
x_119 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 1);
x_120 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 2);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_121 = x_55;
} else {
 lean_dec_ref(x_55);
 x_121 = lean_box(0);
}
x_122 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 8, 1);
lean_closure_set(x_122, 0, x_56);
x_123 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 1, 3);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_118);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 1, x_119);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 2, x_120);
x_125 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_112);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 1, x_113);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 2, x_114);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 3, x_115);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 4, x_116);
x_126 = l_Lake_Workspace_runFetchM___redArg(x_4, x_122, x_125, x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_130);
lean_dec(x_127);
x_131 = lean_io_wait(x_130, x_128);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = l_Lake_Package_test___boxed__const__1;
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_132);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec_ref(x_131);
x_137 = l_Lake_exe___closed__3;
if (lean_is_scalar(x_129)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_129;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_126, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_141 = x_126;
} else {
 lean_dec_ref(x_126);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
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
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_3);
x_184 = lean_ctor_get(x_20, 0);
lean_inc(x_184);
lean_dec_ref(x_20);
x_185 = lean_array_to_list(x_16);
x_186 = l_List_appendTR___redArg(x_185, x_2);
x_187 = l_Lake_Script_run(x_186, x_184, x_4, x_12);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_9);
if (x_188 == 0)
{
return x_9;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_9, 0);
x_190 = lean_ctor_get(x_9, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_9);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
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
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 19);
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
x_17 = lean_ctor_get(x_11, 14);
lean_inc(x_14);
x_28 = l_String_toName(x_14);
x_29 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_28);
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
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_43);
lean_dec(x_41);
x_44 = lean_io_wait(x_43, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_39);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_array_mk(x_2);
x_49 = l_Array_append___redArg(x_15, x_48);
lean_dec_ref(x_48);
x_50 = l_Lake_env(x_47, x_49, x_4, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_45);
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec_ref(x_44);
x_52 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_51);
lean_ctor_set(x_39, 0, x_52);
return x_39;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
lean_dec(x_53);
x_56 = lean_io_wait(x_55, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_array_mk(x_2);
x_61 = l_Array_append___redArg(x_15, x_60);
lean_dec_ref(x_60);
x_62 = l_Lake_env(x_59, x_61, x_4, x_58);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_57);
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec_ref(x_56);
x_64 = l_Lake_exe___closed__3;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_39);
if (x_66 == 0)
{
return x_39;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_39, 0);
x_68 = lean_ctor_get(x_39, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_39);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_3);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
lean_dec_ref(x_29);
x_71 = lean_array_to_list(x_15);
x_72 = l_List_appendTR___redArg(x_71, x_2);
x_73 = l_Lake_Script_run(x_72, x_70, x_4, x_12);
return x_73;
}
block_27:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = 0;
x_19 = l_Lean_Name_toString(x_16, x_18);
x_20 = l_Lake_Package_lint___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_14);
lean_dec(x_14);
x_23 = l_Lake_Package_resolveDriver___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_mk_io_user_error(x_24);
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
uint8_t x_74; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
return x_9;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_9, 0);
x_76 = lean_ctor_get(x_9, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_9);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_io_wait(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_15);
x_16 = lean_io_process_spawn(x_15, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_19);
lean_dec(x_15);
x_20 = lean_io_process_child_wait(x_19, x_17, x_18);
lean_dec(x_17);
lean_dec_ref(x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_13);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec_ref(x_12);
x_26 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_io_wait(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc(x_33);
x_34 = lean_io_process_spawn(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_37);
lean_dec(x_33);
x_38 = lean_io_process_child_wait(x_37, x_35, x_36);
lean_dec(x_35);
lean_dec_ref(x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_31);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec_ref(x_30);
x_44 = l_Lake_exe___closed__3;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
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
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
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
