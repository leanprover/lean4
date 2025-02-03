// Lean compiler output
// Module: Lake.Build.Job.Register
// Imports: Lake.Build.Fetch
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
static lean_object* l_Lake_JobState_renew___closed__1;
LEAN_EXPORT lean_object* l_Lake_registerJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_ensureJob___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___rarg___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__5(lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_ensureJob___spec__4(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1;
extern lean_object* l_Lake_BuildTrace_nil;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_ensureJob___rarg___closed__2;
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__6(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Job_renew___rarg___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_JobState_renew___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lake_JobState_renew___closed__1;
x_5 = 0;
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lake_JobState_renew___closed__1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l_Lake_JobState_renew___closed__1;
x_7 = 0;
lean_ctor_set(x_3, 0, x_6);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lake_JobState_renew___closed__1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = l_Lake_JobState_renew___closed__1;
x_17 = 0;
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 1);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lake_JobState_renew___closed__1;
x_26 = 0;
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_26);
x_27 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lake_JobState_renew___closed__1;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = l_Lake_JobState_renew___closed__1;
x_37 = 0;
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 1);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
static lean_object* _init_l_Lake_Job_renew___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Job_renew___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lake_Job_renew___rarg___closed__1;
x_5 = l_Task_Priority_default;
x_6 = 1;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Lake_Job_renew___rarg___closed__1;
x_12 = l_Task_Priority_default;
x_13 = 1;
x_14 = lean_task_map(x_11, x_8, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Job_renew___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_3);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_st_ref_take(x_12, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
x_17 = lean_array_push(x_15, x_2);
x_18 = lean_st_ref_set(x_12, x_17, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Lake_Job_renew___rarg(x_2);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 0, x_21);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lake_Job_renew___rarg(x_2);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_2);
x_27 = lean_array_push(x_25, x_2);
x_28 = lean_st_ref_set(x_12, x_27, x_26);
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
x_31 = l_Lake_Job_renew___rarg(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_3);
x_36 = lean_ctor_get(x_7, 3);
x_37 = lean_st_ref_take(x_36, x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
lean_inc(x_35);
x_41 = lean_array_push(x_38, x_35);
x_42 = lean_st_ref_set(x_36, x_41, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = l_Lake_Job_renew___rarg(x_35);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_registerJob___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_registerJob___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_ensureJob___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_ensureJob___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_ensureJob___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_ensureJob___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_ensureJob___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_ensureJob___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_ensureJob___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_ensureJob___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_ensureJob___spec__6___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_mk_ref(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_11);
lean_inc(x_14);
x_17 = l_IO_FS_Stream_ofBuffer(x_14);
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_ensureJob___spec__2___rarg), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at_Lake_ensureJob___spec__3___rarg(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_string_validate_utf8(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_30 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_31 = l_panic___at_String_fromUTF8_x21___spec__1(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_20, 0, x_32);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_string_from_utf8_unchecked(x_28);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_20, 0, x_34);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_40 = l_panic___at_String_fromUTF8_x21___spec__1(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_20, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_string_from_utf8_unchecked(x_37);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_23);
lean_ctor_set(x_20, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_23);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_string_validate_utf8(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_58 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_59 = l_panic___at_String_fromUTF8_x21___spec__1(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_55;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_string_from_utf8_unchecked(x_56);
lean_dec(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_51);
lean_dec(x_50);
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_69 = x_52;
} else {
 lean_dec_ref(x_52);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_14);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_20);
if (x_73 == 0)
{
return x_19;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_20, 0);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_20);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_19, 0, x_76);
return x_19;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_80 = x_20;
} else {
 lean_dec_ref(x_20);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_14);
x_83 = !lean_is_exclusive(x_19);
if (x_83 == 0)
{
return x_19;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_17);
x_87 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_ensureJob___spec__4___rarg), 8, 2);
lean_closure_set(x_87, 0, x_17);
lean_closure_set(x_87, 1, x_1);
x_88 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_ensureJob___spec__5___rarg), 8, 2);
lean_closure_set(x_88, 0, x_17);
lean_closure_set(x_88, 1, x_87);
x_89 = l_IO_withStdin___at_Lake_ensureJob___spec__6___rarg(x_16, x_88, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
x_95 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_string_validate_utf8(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
x_100 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_101 = l_panic___at_String_fromUTF8_x21___spec__1(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_90, 0, x_102);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_string_from_utf8_unchecked(x_98);
lean_dec(x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_90, 0, x_104);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_string_validate_utf8(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
x_109 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_110 = l_panic___at_String_fromUTF8_x21___spec__1(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_93);
lean_ctor_set(x_90, 0, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_90);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_string_from_utf8_unchecked(x_107);
lean_dec(x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_90, 0, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_90);
lean_dec(x_94);
lean_dec(x_93);
x_116 = !lean_is_exclusive(x_95);
if (x_116 == 0)
{
return x_95;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_95, 0);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_95);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_120);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_string_from_utf8_unchecked(x_126);
lean_dec(x_126);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_125;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_124);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_121);
lean_dec(x_120);
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_14);
x_141 = !lean_is_exclusive(x_89);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_89, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_90);
if (x_143 == 0)
{
return x_89;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_90, 0);
x_145 = lean_ctor_get(x_90, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_90);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_89, 0, x_146);
return x_89;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_89, 1);
lean_inc(x_147);
lean_dec(x_89);
x_148 = lean_ctor_get(x_90, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_90, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_150 = x_90;
} else {
 lean_dec_ref(x_90);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_14);
x_153 = !lean_is_exclusive(x_89);
if (x_153 == 0)
{
return x_89;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_89, 0);
x_155 = lean_ctor_get(x_89, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_89);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_13);
if (x_157 == 0)
{
return x_13;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_13);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_10);
if (x_161 == 0)
{
return x_10;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_10, 0);
x_163 = lean_ctor_get(x_10, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_10);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_ensureJob___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_85; lean_object* x_86; 
x_8 = lean_array_get_size(x_6);
x_85 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_86 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg(x_1, x_85, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_string_utf8_byte_size(x_91);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_91, x_93, x_94);
x_97 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_91, x_96, x_93);
x_98 = lean_string_utf8_extract(x_91, x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_91);
x_99 = l_Lake_ensureJob___rarg___closed__2;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = l_Lake_ensureJob___rarg___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = 1;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_push(x_90, x_104);
x_106 = lean_box(0);
x_107 = l_Lake_ensureJob___rarg___lambda__1(x_92, x_106, x_2, x_3, x_4, x_5, x_105, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_9 = x_108;
x_10 = x_109;
goto block_84;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_93);
lean_dec(x_91);
x_110 = lean_box(0);
x_111 = l_Lake_ensureJob___rarg___lambda__1(x_92, x_110, x_2, x_3, x_4, x_5, x_90, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_9 = x_112;
x_10 = x_113;
goto block_84;
}
}
else
{
lean_object* x_114; uint8_t x_115; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_86, 1);
lean_inc(x_114);
lean_dec(x_86);
x_115 = !lean_is_exclusive(x_87);
if (x_115 == 0)
{
x_9 = x_87;
x_10 = x_114;
goto block_84;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_87, 0);
x_117 = lean_ctor_get(x_87, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_87);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_9 = x_118;
x_10 = x_114;
goto block_84;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_86);
if (x_119 == 0)
{
return x_86;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_86, 0);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_86);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
block_84:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_13);
x_17 = l_Array_shrink___rarg(x_13, x_8);
x_18 = l_Array_extract___rarg(x_13, x_8, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = l_Task_Priority_default;
x_23 = 1;
x_24 = lean_task_map(x_19, x_21, x_22, x_23);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_9, 1, x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_29 = l_Task_Priority_default;
x_30 = 1;
x_31 = lean_task_map(x_19, x_26, x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_28);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_8, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_35);
x_40 = l_Array_shrink___rarg(x_35, x_8);
x_41 = l_Array_extract___rarg(x_35, x_8, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_42 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_34, sizeof(void*)*2);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_46 = x_34;
} else {
 lean_dec_ref(x_34);
 x_46 = lean_box(0);
}
x_47 = l_Task_Priority_default;
x_48 = 1;
x_49 = lean_task_map(x_42, x_43, x_47, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 2, 1);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_10);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_9, 1);
x_55 = lean_ctor_get(x_9, 0);
lean_dec(x_55);
lean_inc(x_54);
x_56 = l_Array_shrink___rarg(x_54, x_8);
x_57 = lean_array_get_size(x_54);
x_58 = l_Array_extract___rarg(x_54, x_8, x_57);
lean_dec(x_57);
lean_dec(x_54);
x_59 = 0;
x_60 = l_Lake_BuildTrace_nil;
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_59);
x_62 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_9, 1, x_61);
lean_ctor_set(x_9, 0, x_62);
x_63 = lean_task_pure(x_9);
x_64 = l_Lake_ensureJob___rarg___closed__1;
x_65 = 0;
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_10);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_dec(x_9);
lean_inc(x_69);
x_70 = l_Array_shrink___rarg(x_69, x_8);
x_71 = lean_array_get_size(x_69);
x_72 = l_Array_extract___rarg(x_69, x_8, x_71);
lean_dec(x_71);
lean_dec(x_69);
x_73 = 0;
x_74 = l_Lake_BuildTrace_nil;
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_73);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_task_pure(x_77);
x_79 = l_Lake_ensureJob___rarg___closed__1;
x_80 = 0;
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_70);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ensureJob___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lake_ensureJob___rarg(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lake_registerJob___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_14, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_withRegisterJob___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_withRegisterJob___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = l_Lake_registerJob___rarg(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_maybeRegisterJob___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_maybeRegisterJob___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_JobState_renew___closed__1 = _init_l_Lake_JobState_renew___closed__1();
lean_mark_persistent(l_Lake_JobState_renew___closed__1);
l_Lake_Job_renew___rarg___closed__1 = _init_l_Lake_Job_renew___rarg___closed__1();
lean_mark_persistent(l_Lake_Job_renew___rarg___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_ensureJob___spec__1___rarg___closed__5);
l_Lake_ensureJob___rarg___closed__1 = _init_l_Lake_ensureJob___rarg___closed__1();
lean_mark_persistent(l_Lake_ensureJob___rarg___closed__1);
l_Lake_ensureJob___rarg___closed__2 = _init_l_Lake_ensureJob___rarg___closed__2();
lean_mark_persistent(l_Lake_ensureJob___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
