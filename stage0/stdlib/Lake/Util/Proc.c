// Lean compiler output
// Module: Lake.Util.Proc
// Imports: Init Lake.Util.Log
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
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_proc___closed__2;
static lean_object* l_Lake_proc___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object*);
lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_proc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_rawProc___lambda__1___closed__2;
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__3;
static lean_object* l_Lake_rawProc___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__2;
LEAN_EXPORT lean_object* l_Lake_captureProc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_logOutput___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_testProc(lean_object*, lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__1;
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_logOutput___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__4;
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PATH", 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PATH ", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_12 = lean_string_append(x_11, x_7);
lean_dec(x_7);
x_13 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3;
x_14 = lean_string_append(x_12, x_13);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_append(x_14, x_11);
x_16 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
x_17 = lean_string_append(x_15, x_16);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_string_append(x_14, x_19);
lean_dec(x_19);
x_21 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_22);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
x_24 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5;
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_24);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1;
x_31 = lean_string_dec_eq(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_33 = lean_string_append(x_32, x_28);
lean_dec(x_28);
x_34 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3;
x_35 = lean_string_append(x_33, x_34);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_string_append(x_35, x_32);
x_37 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
x_1 = x_27;
x_2 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_string_append(x_35, x_41);
lean_dec(x_41);
x_43 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_2);
x_1 = x_27;
x_2 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_29);
lean_dec(x_28);
x_47 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_2);
x_1 = x_27;
x_2 = x_48;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lake_mkCmdLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkCmdLog___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_2 = l_Lake_mkCmdLog___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_mkCmdLog___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("> ", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_mkCmdLog___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mkCmdLog___closed__2;
x_2 = l_Lake_mkCmdLog___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1(x_3, x_4);
x_6 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_7 = l_List_foldl___at_String_join___spec__1(x_6, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_array_to_list(lean_box(0), x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
x_13 = l_String_intercalate(x_12, x_11);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lake_mkCmdLog___closed__4;
x_16 = lean_string_append(x_15, x_7);
lean_dec(x_7);
x_17 = lean_string_append(x_16, x_6);
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
x_19 = lean_string_append(x_18, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_string_append(x_6, x_20);
lean_dec(x_20);
x_22 = l_Lake_mkCmdLog___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_7);
lean_dec(x_7);
x_25 = lean_string_append(x_24, x_6);
x_26 = lean_string_append(x_25, x_13);
lean_dec(x_13);
x_27 = lean_string_append(x_26, x_6);
return x_27;
}
}
}
static lean_object* _init_l_Lake_logOutput___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stderr:\n", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_String_isEmpty(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_7 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_8 = lean_string_append(x_7, x_5);
x_9 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lake_logOutput___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stdout:\n", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_logOutput___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_String_isEmpty(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lake_logOutput___rarg___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_logOutput___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logOutput___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_rawProc___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to execute '", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_rawProc___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_IO_Process_output(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_rawProc___lambda__1___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_rawProc___lambda__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_io_error_to_string(x_15);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_push(x_4, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lake_rawProc___lambda__1___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lake_rawProc___lambda__1___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_io_error_to_string(x_29);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_push(x_4, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_get_size(x_3);
if (x_2 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = l_Lake_mkCmdLog(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_box(0);
x_11 = l_Lake_rawProc___lambda__1(x_1, x_5, x_10, x_9, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lake_rawProc___lambda__1(x_1, x_5, x_12, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_rawProc___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_rawProc(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_String_isEmpty(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_9 = lean_string_append(x_8, x_6);
x_10 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
if (x_2 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = 1;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_array_push(x_4, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = 0;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_push(x_4, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
static lean_object* _init_l_Lake_proc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("external command '", 18);
return x_1;
}
}
static lean_object* _init_l_Lake_proc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' exited with code ", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_array_get_size(x_3);
lean_inc(x_1);
x_6 = l_Lake_mkCmdLog(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_box(0);
lean_inc(x_5);
lean_inc(x_1);
x_11 = l_Lake_rawProc___lambda__1(x_1, x_5, x_10, x_9, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_64 = lean_ctor_get(x_15, 0);
lean_inc(x_64);
x_65 = l_String_isEmpty(x_64);
if (x_2 == 0)
{
uint8_t x_86; 
x_86 = 0;
x_66 = x_86;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = 1;
x_66 = x_87;
goto block_85;
}
block_63:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_23 = 0;
x_24 = lean_uint32_dec_eq(x_22, x_23);
x_25 = l_instDecidableNot___rarg(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_10);
if (lean_is_scalar(x_14)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_14;
}
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_proc___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lake_proc___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_uint32_to_nat(x_22);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_20, x_38);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_39);
lean_ctor_set(x_17, 0, x_5);
if (lean_is_scalar(x_14)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_14;
}
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_18);
return x_40;
}
}
else
{
lean_object* x_41; uint32_t x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get_uint32(x_15, sizeof(void*)*2);
lean_dec(x_15);
x_43 = 0;
x_44 = lean_uint32_dec_eq(x_42, x_43);
x_45 = l_instDecidableNot___rarg(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_41);
if (lean_is_scalar(x_14)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_14;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_18);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Lake_proc___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lake_proc___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_uint32_to_nat(x_42);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_53);
x_55 = lean_string_append(x_52, x_54);
lean_dec(x_54);
x_56 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_57 = lean_string_append(x_55, x_56);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_push(x_41, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_14)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_14;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_18);
return x_62;
}
}
}
block_85:
{
if (x_65 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = l_Lake_logOutput___rarg___closed__1;
x_68 = lean_string_append(x_67, x_64);
lean_dec(x_64);
x_69 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_70 = lean_string_append(x_68, x_69);
if (x_66 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = 1;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_push(x_16, x_72);
x_74 = l_Lake_proc___lambda__1(x_15, x_66, x_10, x_73, x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_17 = x_75;
x_18 = x_76;
goto block_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_7);
x_78 = lean_array_push(x_16, x_77);
x_79 = l_Lake_proc___lambda__1(x_15, x_66, x_10, x_78, x_13);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_17 = x_80;
x_18 = x_81;
goto block_63;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
x_82 = l_Lake_proc___lambda__1(x_15, x_66, x_10, x_16, x_13);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_17 = x_83;
x_18 = x_84;
goto block_63;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_11);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_11, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_12);
if (x_90 == 0)
{
return x_11;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_12, 0);
x_92 = lean_ctor_get(x_12, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_12);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_11, 0, x_93);
return x_11;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_dec(x_11);
x_95 = lean_ctor_get(x_12, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_12, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_97 = x_12;
} else {
 lean_dec_ref(x_12);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_proc___lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_proc(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_String_isEmpty(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_8 = lean_string_append(x_7, x_5);
x_9 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_box(0);
lean_inc(x_1);
x_6 = l_Lake_rawProc___lambda__1(x_1, x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get_uint32(x_11, sizeof(void*)*2);
x_14 = 0;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_7);
lean_inc(x_1);
x_16 = l_Lake_mkCmdLog(x_1);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_12);
x_29 = lean_array_push(x_12, x_18);
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
x_31 = l_String_isEmpty(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = l_Lake_logOutput___rarg___closed__1;
x_33 = lean_string_append(x_32, x_30);
lean_dec(x_30);
x_34 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_push(x_29, x_37);
x_39 = l_Lake_captureProc___lambda__1(x_11, x_5, x_38, x_8);
lean_dec(x_11);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lake_proc___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lake_proc___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_uint32_to_nat(x_13);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_50);
x_52 = lean_string_append(x_49, x_51);
lean_dec(x_51);
x_53 = lean_string_append(x_52, x_34);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_push(x_43, x_55);
lean_ctor_set(x_40, 1, x_56);
lean_ctor_set(x_40, 0, x_5);
x_20 = x_40;
x_21 = x_41;
goto block_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l_Lake_proc___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lake_proc___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_uint32_to_nat(x_13);
x_64 = l___private_Init_Data_Repr_0__Nat_reprFast(x_63);
x_65 = lean_string_append(x_62, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_34);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_push(x_57, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_69);
x_20 = x_70;
x_21 = x_41;
goto block_28;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_30);
x_71 = l_Lake_captureProc___lambda__1(x_11, x_5, x_29, x_8);
lean_dec(x_11);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_72, 1);
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
lean_dec(x_1);
x_78 = l_Lake_proc___closed__1;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lake_proc___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_uint32_to_nat(x_13);
x_83 = l___private_Init_Data_Repr_0__Nat_reprFast(x_82);
x_84 = lean_string_append(x_81, x_83);
lean_dec(x_83);
x_85 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_push(x_75, x_88);
lean_ctor_set(x_72, 1, x_89);
lean_ctor_set(x_72, 0, x_5);
x_20 = x_72;
x_21 = x_73;
goto block_28;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
lean_dec(x_72);
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lake_proc___closed__1;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lake_proc___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_uint32_to_nat(x_13);
x_97 = l___private_Init_Data_Repr_0__Nat_reprFast(x_96);
x_98 = lean_string_append(x_95, x_97);
lean_dec(x_97);
x_99 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_100 = lean_string_append(x_98, x_99);
x_101 = 3;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
x_103 = lean_array_push(x_90, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_103);
x_20 = x_104;
x_21 = x_73;
goto block_28;
}
}
block_28:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
if (lean_is_scalar(x_9)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_9;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_105 = lean_ctor_get(x_11, 0);
lean_inc(x_105);
lean_dec(x_11);
x_106 = l_String_trim(x_105);
lean_dec(x_105);
lean_ctor_set(x_7, 0, x_106);
if (lean_is_scalar(x_9)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_9;
}
lean_ctor_set(x_107, 0, x_7);
lean_ctor_set(x_107, 1, x_8);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint32_t x_110; uint32_t x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_7, 0);
x_109 = lean_ctor_get(x_7, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_7);
x_110 = lean_ctor_get_uint32(x_108, sizeof(void*)*2);
x_111 = 0;
x_112 = lean_uint32_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_inc(x_1);
x_113 = l_Lake_mkCmdLog(x_1);
x_114 = 0;
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
x_116 = lean_array_get_size(x_109);
x_124 = lean_array_push(x_109, x_115);
x_125 = lean_ctor_get(x_108, 0);
lean_inc(x_125);
x_126 = l_String_isEmpty(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_127 = l_Lake_logOutput___rarg___closed__1;
x_128 = lean_string_append(x_127, x_125);
lean_dec(x_125);
x_129 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_130 = lean_string_append(x_128, x_129);
x_131 = 1;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_push(x_124, x_132);
x_134 = l_Lake_captureProc___lambda__1(x_108, x_5, x_133, x_8);
lean_dec(x_108);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
lean_dec(x_1);
x_140 = l_Lake_proc___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lake_proc___closed__2;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_uint32_to_nat(x_110);
x_145 = l___private_Init_Data_Repr_0__Nat_reprFast(x_144);
x_146 = lean_string_append(x_143, x_145);
lean_dec(x_145);
x_147 = lean_string_append(x_146, x_129);
x_148 = 3;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_push(x_137, x_149);
if (lean_is_scalar(x_138)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_138;
}
lean_ctor_set(x_151, 0, x_5);
lean_ctor_set(x_151, 1, x_150);
x_117 = x_151;
x_118 = x_136;
goto block_123;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_125);
x_152 = l_Lake_captureProc___lambda__1(x_108, x_5, x_124, x_8);
lean_dec(x_108);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
lean_dec(x_1);
x_158 = l_Lake_proc___closed__1;
x_159 = lean_string_append(x_158, x_157);
lean_dec(x_157);
x_160 = l_Lake_proc___closed__2;
x_161 = lean_string_append(x_159, x_160);
x_162 = lean_uint32_to_nat(x_110);
x_163 = l___private_Init_Data_Repr_0__Nat_reprFast(x_162);
x_164 = lean_string_append(x_161, x_163);
lean_dec(x_163);
x_165 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_166 = lean_string_append(x_164, x_165);
x_167 = 3;
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_167);
x_169 = lean_array_push(x_155, x_168);
if (lean_is_scalar(x_156)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_156;
}
lean_ctor_set(x_170, 0, x_5);
lean_ctor_set(x_170, 1, x_169);
x_117 = x_170;
x_118 = x_154;
goto block_123;
}
block_123:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_119);
if (lean_is_scalar(x_9)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_9;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_118);
return x_122;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_108, 0);
lean_inc(x_171);
lean_dec(x_108);
x_172 = l_String_trim(x_171);
lean_dec(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_109);
if (lean_is_scalar(x_9)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_9;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_8);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_6);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_6, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_7);
if (x_177 == 0)
{
return x_6;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_7, 0);
x_179 = lean_ctor_get(x_7, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_7);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_6, 0, x_180);
return x_6;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_6, 1);
lean_inc(x_181);
lean_dec(x_6);
x_182 = lean_ctor_get(x_7, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_7, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_184 = x_7;
} else {
 lean_dec_ref(x_7);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
return x_186;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_captureProc___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_7 = 0;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_String_trim(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_ctor_get_uint32(x_13, sizeof(void*)*2);
x_16 = 0;
x_17 = lean_uint32_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l_String_trim(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 2;
lean_ctor_set_uint8(x_4, 1, x_6);
lean_ctor_set_uint8(x_4, 2, x_6);
lean_inc(x_4);
x_7 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_io_process_child_wait(x_4, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = 0;
x_14 = lean_unbox_uint32(x_12);
lean_dec(x_12);
x_15 = lean_uint32_dec_eq(x_14, x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; uint32_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = 0;
x_20 = lean_unbox_uint32(x_17);
lean_dec(x_17);
x_21 = lean_uint32_dec_eq(x_20, x_19);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_27);
return x_10;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_dec(x_7);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_41 = 2;
x_42 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, 2, x_41);
lean_inc(x_42);
lean_ctor_set(x_1, 0, x_42);
x_43 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_io_process_child_wait(x_42, x_44, x_45);
lean_dec(x_44);
lean_dec(x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; uint32_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = 0;
x_51 = lean_unbox_uint32(x_47);
lean_dec(x_47);
x_52 = lean_uint32_dec_eq(x_51, x_50);
x_53 = lean_box(x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
x_57 = 0;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
 lean_ctor_set_tag(x_59, 0);
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_61 = x_43;
} else {
 lean_dec_ref(x_43);
 x_61 = lean_box(0);
}
x_62 = 0;
x_63 = lean_box(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
 lean_ctor_set_tag(x_64, 0);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = lean_ctor_get(x_1, 1);
x_67 = lean_ctor_get(x_1, 2);
x_68 = lean_ctor_get(x_1, 3);
x_69 = lean_ctor_get(x_1, 4);
x_70 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_1);
x_71 = lean_ctor_get_uint8(x_65, 0);
if (lean_is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
x_73 = 2;
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 0, 3);
} else {
 x_74 = x_72;
}
lean_ctor_set_uint8(x_74, 0, x_71);
lean_ctor_set_uint8(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, 2, x_73);
lean_inc(x_74);
x_75 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_69);
lean_ctor_set_uint8(x_75, sizeof(void*)*5, x_70);
x_76 = lean_io_process_spawn(x_75, x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_io_process_child_wait(x_74, x_77, x_78);
lean_dec(x_77);
lean_dec(x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; uint32_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = 0;
x_84 = lean_unbox_uint32(x_80);
lean_dec(x_80);
x_85 = lean_uint32_dec_eq(x_84, x_83);
x_86 = lean_box(x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
x_90 = 0;
x_91 = lean_box(x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
 lean_ctor_set_tag(x_92, 0);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
x_95 = 0;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1 = _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1);
l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2 = _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2);
l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3 = _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3);
l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4 = _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4);
l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5 = _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5();
lean_mark_persistent(l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5);
l_Lake_mkCmdLog___closed__1 = _init_l_Lake_mkCmdLog___closed__1();
lean_mark_persistent(l_Lake_mkCmdLog___closed__1);
l_Lake_mkCmdLog___closed__2 = _init_l_Lake_mkCmdLog___closed__2();
lean_mark_persistent(l_Lake_mkCmdLog___closed__2);
l_Lake_mkCmdLog___closed__3 = _init_l_Lake_mkCmdLog___closed__3();
lean_mark_persistent(l_Lake_mkCmdLog___closed__3);
l_Lake_mkCmdLog___closed__4 = _init_l_Lake_mkCmdLog___closed__4();
lean_mark_persistent(l_Lake_mkCmdLog___closed__4);
l_Lake_logOutput___rarg___lambda__1___closed__1 = _init_l_Lake_logOutput___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lake_logOutput___rarg___lambda__1___closed__1);
l_Lake_logOutput___rarg___closed__1 = _init_l_Lake_logOutput___rarg___closed__1();
lean_mark_persistent(l_Lake_logOutput___rarg___closed__1);
l_Lake_rawProc___lambda__1___closed__1 = _init_l_Lake_rawProc___lambda__1___closed__1();
lean_mark_persistent(l_Lake_rawProc___lambda__1___closed__1);
l_Lake_rawProc___lambda__1___closed__2 = _init_l_Lake_rawProc___lambda__1___closed__2();
lean_mark_persistent(l_Lake_rawProc___lambda__1___closed__2);
l_Lake_proc___closed__1 = _init_l_Lake_proc___closed__1();
lean_mark_persistent(l_Lake_proc___closed__1);
l_Lake_proc___closed__2 = _init_l_Lake_proc___closed__2();
lean_mark_persistent(l_Lake_proc___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
