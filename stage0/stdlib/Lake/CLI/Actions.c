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
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__1;
static lean_object* l_Lake_Package_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__1;
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_Package_resolveDriver_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_unpack___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_exe___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__2;
static lean_object* l_Lake_Package_test___closed__3;
static lean_object* l_Lake_exe___closed__0;
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__5;
lean_object* lean_io_process_spawn(lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__1;
LEAN_EXPORT lean_object* l_Lake_env___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__4;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_lint___closed__0;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__2;
lean_object* l_Lake_buildSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_unpack___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__5;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_uploadRelease___closed__6;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_Package_pack___closed__0;
lean_object* l_Lake_prepareLeanCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_resolveDriver___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__12;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
static lean_object* l_Lake_Package_uploadRelease___closed__7;
static lean_object* l_Lake_Package_uploadRelease___closed__13;
LEAN_EXPORT lean_object* l_Lake_exe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_env___closed__0;
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_env(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = lean_io_process_spawn(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_io_process_child_wait(x_6, x_12);
lean_dec(x_12);
return x_13;
}
else
{
uint8_t x_14; 
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
}
LEAN_EXPORT lean_object* l_Lake_env___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_env(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lake_exe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec_ref(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 8, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_4);
x_17 = l_Lake_Workspace_runFetchM___redArg(x_4, x_16, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_io_wait(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lake_env(x_22, x_2, x_4);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_21);
lean_dec(x_4);
lean_dec_ref(x_2);
x_24 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
lean_dec(x_25);
x_27 = lean_io_wait(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lake_env(x_28, x_2, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_27);
lean_dec(x_4);
lean_dec_ref(x_2);
x_30 = l_Lake_exe___closed__3;
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
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
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_exe___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_exe(x_1, x_2, x_3, x_4);
return x_6;
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
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Lake_tar(x_14, x_2, x_15, x_16, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_pack(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_16 = l_Lake_untar(x_2, x_14, x_15, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_unpack(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_23 = l_Lake_Package_pack(x_1, x_22, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_18, 11);
lean_inc(x_25);
lean_dec_ref(x_18);
x_26 = l_Lake_Package_uploadRelease___closed__3;
x_27 = lean_string_append(x_26, x_2);
x_28 = l_Lake_Package_uploadRelease___closed__4;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_19);
lean_dec_ref(x_19);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_push(x_24, x_32);
x_34 = l_Lake_Package_uploadRelease___closed__7;
x_35 = l_Lake_Package_uploadRelease___closed__10;
x_36 = lean_array_push(x_35, x_2);
x_37 = lean_array_push(x_36, x_22);
x_38 = lean_array_push(x_37, x_34);
if (lean_obj_tag(x_25) == 0)
{
x_5 = x_38;
x_6 = x_33;
x_7 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec_ref(x_25);
x_40 = l_Lake_Package_uploadRelease___closed__13;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Array_append___redArg(x_38, x_41);
lean_dec_ref(x_41);
x_5 = x_42;
x_6 = x_33;
x_7 = lean_box(0);
goto block_16;
}
}
else
{
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
x_15 = l_Lake_proc(x_14, x_13, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_uploadRelease(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_box(0);
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
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_25);
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
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
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
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec_ref(x_25);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_4, 5);
lean_inc(x_35);
x_40 = l_String_toName(x_35);
x_41 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_39, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_26);
lean_dec(x_37);
x_42 = l_Lake_Package_resolveDriver___closed__3;
x_43 = lean_string_append(x_8, x_42);
x_44 = lean_string_append(x_43, x_2);
x_45 = l_Lake_Package_resolveDriver___closed__4;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_35);
lean_dec(x_35);
x_48 = l_Lake_Package_resolveDriver___closed__5;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_mk_io_user_error(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec_ref(x_8);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_41, 0);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_37);
lean_ctor_set(x_26, 0, x_53);
lean_ctor_set_tag(x_41, 0);
lean_ctor_set(x_41, 0, x_26);
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_37);
lean_ctor_set(x_26, 0, x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_26);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_26, 0);
lean_inc(x_56);
lean_dec(x_26);
x_57 = lean_ctor_get(x_4, 5);
lean_inc(x_35);
x_58 = l_String_toName(x_35);
x_59 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_resolveDriver_spec__1___redArg(x_57, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_56);
x_60 = l_Lake_Package_resolveDriver___closed__3;
x_61 = lean_string_append(x_8, x_60);
x_62 = lean_string_append(x_61, x_2);
x_63 = l_Lake_Package_resolveDriver___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_35);
lean_dec(x_35);
x_66 = l_Lake_Package_resolveDriver___closed__5;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_mk_io_user_error(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_35);
lean_dec_ref(x_8);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_71 = x_59;
} else {
 lean_dec_ref(x_59);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_56);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_71;
 lean_ctor_set_tag(x_73, 0);
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_9 = lean_box(0);
goto block_20;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_1);
x_74 = l_Lake_Package_resolveDriver___closed__6;
x_75 = lean_string_append(x_8, x_74);
x_76 = lean_string_append(x_75, x_2);
x_77 = l_Lake_Package_resolveDriver___closed__7;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_mk_io_user_error(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
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
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
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
x_6 = l_Lake_Package_resolveDriver(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = lean_apply_7(x_5, x_14, x_6, x_7, x_8, x_9, x_10, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_7);
x_8 = l_Lake_Package_test___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4);
lean_dec_ref(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_6, 14);
lean_inc_ref(x_14);
lean_dec_ref(x_6);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 14);
lean_inc(x_13);
x_17 = l_String_toName(x_13);
x_18 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_130; 
x_19 = 0;
lean_inc(x_15);
x_20 = l_Lean_Name_toString(x_15, x_19);
x_130 = l_Lake_Package_findTargetDecl_x3f(x_17, x_12);
if (lean_obj_tag(x_130) == 0)
{
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 3);
lean_inc(x_134);
lean_dec(x_131);
x_135 = l_Lake_LeanExe_keyword;
x_136 = lean_name_eq(x_133, x_135);
lean_dec(x_133);
if (x_136 == 0)
{
lean_dec(x_134);
lean_dec(x_132);
goto block_129;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_20);
lean_dec(x_17);
lean_inc(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_132);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_12);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_137, 2, x_134);
x_138 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(x_138, 0, x_15);
lean_closure_set(x_138, 1, x_132);
lean_closure_set(x_138, 2, x_135);
lean_closure_set(x_138, 3, x_137);
lean_inc(x_4);
x_139 = l_Lake_Workspace_runFetchM___redArg(x_4, x_138, x_3);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
lean_dec(x_141);
x_143 = lean_io_wait(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_139);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = lean_array_mk(x_2);
x_146 = l_Array_append___redArg(x_14, x_145);
lean_dec_ref(x_145);
x_147 = l_Lake_env(x_144, x_146, x_4);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec_ref(x_143);
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_148 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_139, 1);
lean_ctor_set(x_139, 0, x_148);
return x_139;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_139, 0);
lean_inc(x_149);
lean_dec(x_139);
x_150 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_150);
lean_dec(x_149);
x_151 = lean_io_wait(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_array_mk(x_2);
x_154 = l_Array_append___redArg(x_14, x_153);
lean_dec_ref(x_153);
x_155 = l_Lake_env(x_152, x_154, x_4);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec_ref(x_151);
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_156 = l_Lake_exe___closed__3;
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_139);
if (x_158 == 0)
{
return x_139;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_139, 0);
lean_inc(x_159);
lean_dec(x_139);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lake_Package_test___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_mk_io_user_error(x_22);
if (lean_is_scalar(x_11)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_11;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
block_33:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lake_Package_test___closed__2;
x_27 = lean_string_append(x_20, x_26);
x_28 = lean_string_append(x_27, x_13);
lean_dec(x_13);
x_29 = l_Lake_Package_resolveDriver___closed__5;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_mk_io_user_error(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
block_129:
{
lean_object* x_34; 
x_34 = l_Lake_Package_findTargetDecl_x3f(x_17, x_12);
lean_dec(x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 3);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lake_Package_test___closed__4;
x_40 = lean_name_eq(x_37, x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_33;
}
else
{
uint8_t x_41; 
lean_dec(x_13);
x_41 = l_Array_isEmpty___redArg(x_14);
lean_dec_ref(x_14);
if (x_41 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_25;
}
else
{
uint8_t x_42; 
x_42 = l_List_isEmpty___redArg(x_2);
lean_dec(x_2);
if (x_42 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_38);
x_44 = lean_box(0);
x_45 = l_Lake_resolveLibTarget(x_4, x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lake_Package_test___closed__5;
x_49 = lean_string_append(x_20, x_48);
x_50 = l_Lake_CliError_toString(x_47);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = lean_mk_io_user_error(x_51);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lake_Package_test___closed__5;
x_55 = lean_string_append(x_20, x_54);
x_56 = l_Lake_CliError_toString(x_53);
x_57 = lean_string_append(x_55, x_56);
lean_dec_ref(x_56);
x_58 = lean_mk_io_user_error(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec_ref(x_20);
x_60 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
lean_dec_ref(x_45);
x_62 = !lean_is_exclusive(x_3);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_3, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_alloc_closure((void*)(l_Lake_buildSpecs___boxed), 8, 1);
lean_closure_set(x_66, 0, x_61);
x_67 = lean_box(0);
lean_ctor_set(x_60, 0, x_67);
x_68 = l_Lake_Workspace_runFetchM___redArg(x_4, x_66, x_3);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_71);
lean_dec(x_70);
x_72 = lean_io_wait(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_dec_ref(x_72);
x_73 = l_Lake_Package_test___boxed__const__1;
lean_ctor_set(x_68, 0, x_73);
return x_68;
}
else
{
lean_object* x_74; 
lean_dec_ref(x_72);
x_74 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 0, x_74);
return x_68;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
lean_dec(x_75);
x_77 = lean_io_wait(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = l_Lake_Package_test___boxed__const__1;
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_77);
x_80 = l_Lake_exe___closed__3;
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_68);
if (x_82 == 0)
{
return x_68;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_68, 0);
lean_inc(x_83);
lean_dec(x_68);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
x_86 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 1);
x_87 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 2);
lean_dec(x_60);
x_88 = lean_alloc_closure((void*)(l_Lake_buildSpecs___boxed), 8, 1);
lean_closure_set(x_88, 0, x_61);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*1 + 1, x_86);
lean_ctor_set_uint8(x_90, sizeof(void*)*1 + 2, x_87);
lean_ctor_set(x_3, 0, x_90);
x_91 = l_Lake_Workspace_runFetchM___redArg(x_4, x_88, x_3);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_94);
lean_dec(x_92);
x_95 = lean_io_wait(x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_95);
x_96 = l_Lake_Package_test___boxed__const__1;
if (lean_is_scalar(x_93)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_93;
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_95);
x_98 = l_Lake_exe___closed__3;
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_93;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_101 = x_91;
} else {
 lean_dec_ref(x_91);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_103 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_104 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_105 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_106 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_107 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
lean_dec(x_3);
x_109 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
x_110 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 1);
x_111 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 2);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_112 = x_60;
} else {
 lean_dec_ref(x_60);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_closure((void*)(l_Lake_buildSpecs___boxed), 8, 1);
lean_closure_set(x_113, 0, x_61);
x_114 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 1, 3);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_109);
lean_ctor_set_uint8(x_115, sizeof(void*)*1 + 1, x_110);
lean_ctor_set_uint8(x_115, sizeof(void*)*1 + 2, x_111);
x_116 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_103);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 1, x_104);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 2, x_105);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 3, x_106);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 4, x_107);
x_117 = l_Lake_Workspace_runFetchM___redArg(x_4, x_113, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
lean_dec(x_118);
x_121 = lean_io_wait(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_121);
x_122 = l_Lake_Package_test___boxed__const__1;
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec_ref(x_121);
x_124 = l_Lake_exe___closed__3;
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_119;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
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
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_3);
x_161 = lean_ctor_get(x_18, 0);
lean_inc(x_161);
lean_dec_ref(x_18);
x_162 = lean_array_to_list(x_14);
x_163 = l_List_appendTR___redArg(x_162, x_2);
x_164 = l_Lake_Script_run(x_163, x_161, x_4);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_9);
if (x_165 == 0)
{
return x_9;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_9, 0);
lean_inc(x_166);
lean_dec(x_9);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Package_test___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_test(x_1, x_2, x_3, x_4);
return x_6;
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
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 19);
lean_inc_ref(x_7);
x_8 = l_Lake_Package_lint___closed__0;
x_9 = l_Lake_Package_resolveDriver(x_1, x_8, x_7, x_4);
lean_dec_ref(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_6, 16);
lean_inc_ref(x_14);
lean_dec_ref(x_6);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 14);
lean_inc(x_13);
x_27 = l_String_toName(x_13);
x_28 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_16, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Lake_Package_findTargetDecl_x3f(x_27, x_12);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 3);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lake_LeanExe_keyword;
x_35 = lean_name_eq(x_32, x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(x_37, 0, x_15);
lean_closure_set(x_37, 1, x_31);
lean_closure_set(x_37, 2, x_34);
lean_closure_set(x_37, 3, x_36);
lean_inc(x_4);
x_38 = l_Lake_Workspace_runFetchM___redArg(x_4, x_37, x_3);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
lean_dec(x_40);
x_42 = lean_io_wait(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_38);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_array_mk(x_2);
x_45 = l_Array_append___redArg(x_14, x_44);
lean_dec_ref(x_44);
x_46 = l_Lake_env(x_43, x_45, x_4);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec_ref(x_42);
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_47 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = lean_io_wait(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_array_mk(x_2);
x_53 = l_Array_append___redArg(x_14, x_52);
lean_dec_ref(x_52);
x_54 = l_Lake_env(x_51, x_53, x_4);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_50);
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_55 = l_Lake_exe___closed__3;
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_38, 0);
lean_inc(x_58);
lean_dec(x_38);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_3);
x_60 = lean_ctor_get(x_28, 0);
lean_inc(x_60);
lean_dec_ref(x_28);
x_61 = lean_array_to_list(x_14);
x_62 = l_List_appendTR___redArg(x_61, x_2);
x_63 = l_Lake_Script_run(x_62, x_60, x_4);
return x_63;
}
block_26:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = 0;
x_18 = l_Lean_Name_toString(x_15, x_17);
x_19 = l_Lake_Package_lint___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_13);
lean_dec(x_13);
x_22 = l_Lake_Package_resolveDriver___closed__5;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_mk_io_user_error(x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_11;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
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
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_9, 0);
lean_inc(x_65);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_lint(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand___boxed), 9, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lake_Workspace_runFetchM___redArg(x_1, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_io_wait(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_12);
x_13 = lean_io_process_spawn(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_15);
lean_dec(x_12);
x_16 = lean_io_process_child_wait(x_15, x_14);
lean_dec(x_14);
lean_dec_ref(x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec_ref(x_11);
x_20 = l_Lake_exe___closed__3;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_io_wait(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_24);
x_25 = lean_io_process_spawn(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_27);
lean_dec(x_24);
x_28 = lean_io_process_child_wait(x_27, x_26);
lean_dec(x_26);
lean_dec_ref(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_23);
x_32 = l_Lake_exe___closed__3;
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_evalLeanFile(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Build_Run(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
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
