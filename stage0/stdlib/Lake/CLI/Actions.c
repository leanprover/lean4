// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Init Lake.Build.Run Lake.Build.Targets
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___closed__4;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___closed__7;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_uploadRelease___closed__5;
static lean_object* l_Lake_exe___closed__2;
lean_object* l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___lambda__1___closed__6;
static lean_object* l_Lake_exe___closed__4;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_exe___closed__1;
static lean_object* l_Lake_exe___closed__3;
static lean_object* l_Lake_uploadRelease___lambda__1___closed__1;
static lean_object* l_Lake_uploadRelease___closed__9;
static lean_object* l_Lake_uploadRelease___closed__1;
lean_object* l_Lean_RBNode_find___at_Lake_Workspace_findScript_x3f___spec__1(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__2;
LEAN_EXPORT lean_object* l_Lake_uploadRelease___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_test___closed__1;
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___closed__3;
LEAN_EXPORT lean_object* l_Lake_uploadRelease___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_env___closed__1;
static lean_object* l_Lake_uploadRelease___closed__2;
lean_object* l_Lake_LeanExe_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___lambda__1___closed__5;
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___lambda__1___closed__2;
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___closed__8;
static lean_object* l_Lake_uploadRelease___lambda__1___closed__3;
static lean_object* l_Lake_uploadRelease___lambda__1___closed__4;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_uploadRelease___closed__6;
LEAN_EXPORT lean_object* l_Lake_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
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
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lake_exe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown executable `", 20);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_exe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("build failed", 12);
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
lean_inc(x_4);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_wait(x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lake_env(x_24, x_2, x_4, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = l_Lake_exe___closed__4;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lake_exe___closed__4;
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
lean_dec(x_2);
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
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("packing ", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("uploading ", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("gh", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_uploadRelease___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = l_Lake_uploadRelease___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_Lake_uploadRelease___lambda__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_push(x_8, x_15);
x_17 = lean_ctor_get(x_2, 8);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_System_FilePath_join(x_3, x_17);
x_19 = 1;
x_20 = l_Lake_uploadRelease___lambda__1___closed__3;
x_21 = l_Lake_tar(x_18, x_4, x_19, x_20, x_16, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lake_uploadRelease___lambda__1___closed__4;
x_26 = lean_string_append(x_25, x_5);
x_27 = l_Lake_uploadRelease___lambda__1___closed__5;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_1);
x_30 = lean_string_append(x_29, x_12);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_14);
x_32 = lean_array_push(x_24, x_31);
x_33 = lean_box(0);
x_34 = l_Lake_env___closed__1;
x_35 = l_Lake_uploadRelease___lambda__1___closed__6;
x_36 = 0;
x_37 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_6);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_36);
x_38 = l_Lake_proc(x_37, x_36, x_32, x_23);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_21, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_21, 0, x_44);
return x_21;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_48 = x_22;
} else {
 lean_dec_ref(x_22);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("release", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uploadRelease___closed__1;
x_2 = l_Lake_uploadRelease___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("upload", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uploadRelease___closed__3;
x_2 = l_Lake_uploadRelease___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--clobber", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-R", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_uploadRelease___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uploadRelease___closed__7;
x_2 = l_Lake_uploadRelease___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_uploadRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lake_defaultLakeDir;
lean_inc(x_5);
x_7 = l_System_FilePath_join(x_5, x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 16);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_System_FilePath_join(x_7, x_9);
x_11 = l_Lake_uploadRelease___closed__5;
lean_inc(x_2);
x_12 = lean_array_push(x_11, x_2);
lean_inc(x_10);
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lake_uploadRelease___closed__6;
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_ctor_get(x_8, 14);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_8, 13);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lake_uploadRelease___lambda__1(x_9, x_8, x_5, x_10, x_2, x_15, x_18, x_3, x_4);
lean_dec(x_2);
lean_dec(x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_uploadRelease___closed__9;
x_22 = lean_array_push(x_21, x_20);
x_23 = l_Array_append___rarg(x_15, x_22);
x_24 = lean_box(0);
x_25 = l_Lake_uploadRelease___lambda__1(x_9, x_8, x_5, x_10, x_2, x_23, x_24, x_3, x_4);
lean_dec(x_2);
lean_dec(x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lake_uploadRelease___closed__9;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Array_append___rarg(x_15, x_28);
x_30 = lean_box(0);
x_31 = l_Lake_uploadRelease___lambda__1(x_9, x_8, x_5, x_10, x_2, x_29, x_30, x_3, x_4);
lean_dec(x_2);
lean_dec(x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_uploadRelease___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_uploadRelease___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lake_Package_test___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": invalid test runner: unknown script or executable `", 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_test___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": no test runner script or executable", 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = lean_ctor_get(x_1, 16);
lean_inc(x_10);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 13);
lean_inc(x_12);
x_13 = l_Lean_RBNode_find___at_Lake_Workspace_findScript_x3f___spec__1(x_12, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 9);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_RBNode_find___at_Lake_Package_findLeanExe_x3f___spec__1(x_15, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lake_uploadRelease___lambda__1___closed__2;
x_18 = lean_string_append(x_17, x_9);
lean_dec(x_9);
x_19 = l_Lake_Package_test___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = 1;
x_22 = l_Lean_Name_toString(x_10, x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = l_Lake_exe___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lake_LeanExe_fetch), 7, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_4);
x_31 = l_Lake_Workspace_runFetchM___rarg(x_4, x_30, x_3, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_io_wait(x_32, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_List_redLength___rarg(x_2);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
x_41 = l_List_toArrayAux___rarg(x_2, x_40);
x_42 = l_Lake_env(x_38, x_41, x_4, x_36);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = l_Lake_exe___closed__4;
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_45);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = l_Lake_exe___closed__4;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_54 = l_Lake_Script_run(x_2, x_53, x_4, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lake_uploadRelease___lambda__1___closed__2;
x_56 = lean_string_append(x_55, x_9);
lean_dec(x_9);
x_57 = l_Lake_Package_test___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
return x_60;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
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
l_Lake_uploadRelease___lambda__1___closed__1 = _init_l_Lake_uploadRelease___lambda__1___closed__1();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__1);
l_Lake_uploadRelease___lambda__1___closed__2 = _init_l_Lake_uploadRelease___lambda__1___closed__2();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__2);
l_Lake_uploadRelease___lambda__1___closed__3 = _init_l_Lake_uploadRelease___lambda__1___closed__3();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__3);
l_Lake_uploadRelease___lambda__1___closed__4 = _init_l_Lake_uploadRelease___lambda__1___closed__4();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__4);
l_Lake_uploadRelease___lambda__1___closed__5 = _init_l_Lake_uploadRelease___lambda__1___closed__5();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__5);
l_Lake_uploadRelease___lambda__1___closed__6 = _init_l_Lake_uploadRelease___lambda__1___closed__6();
lean_mark_persistent(l_Lake_uploadRelease___lambda__1___closed__6);
l_Lake_uploadRelease___closed__1 = _init_l_Lake_uploadRelease___closed__1();
lean_mark_persistent(l_Lake_uploadRelease___closed__1);
l_Lake_uploadRelease___closed__2 = _init_l_Lake_uploadRelease___closed__2();
lean_mark_persistent(l_Lake_uploadRelease___closed__2);
l_Lake_uploadRelease___closed__3 = _init_l_Lake_uploadRelease___closed__3();
lean_mark_persistent(l_Lake_uploadRelease___closed__3);
l_Lake_uploadRelease___closed__4 = _init_l_Lake_uploadRelease___closed__4();
lean_mark_persistent(l_Lake_uploadRelease___closed__4);
l_Lake_uploadRelease___closed__5 = _init_l_Lake_uploadRelease___closed__5();
lean_mark_persistent(l_Lake_uploadRelease___closed__5);
l_Lake_uploadRelease___closed__6 = _init_l_Lake_uploadRelease___closed__6();
lean_mark_persistent(l_Lake_uploadRelease___closed__6);
l_Lake_uploadRelease___closed__7 = _init_l_Lake_uploadRelease___closed__7();
lean_mark_persistent(l_Lake_uploadRelease___closed__7);
l_Lake_uploadRelease___closed__8 = _init_l_Lake_uploadRelease___closed__8();
lean_mark_persistent(l_Lake_uploadRelease___closed__8);
l_Lake_uploadRelease___closed__9 = _init_l_Lake_uploadRelease___closed__9();
lean_mark_persistent(l_Lake_uploadRelease___closed__9);
l_Lake_Package_test___closed__1 = _init_l_Lake_Package_test___closed__1();
lean_mark_persistent(l_Lake_Package_test___closed__1);
l_Lake_Package_test___closed__2 = _init_l_Lake_Package_test___closed__2();
lean_mark_persistent(l_Lake_Package_test___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
