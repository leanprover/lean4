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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_proc___closed__2;
static lean_object* l_Lake_proc___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_proc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_testProc___closed__1;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* lean_array_to_list(lean_object*);
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
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_logOutput___rarg___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__1;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH ", 5, 5);
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
x_1 = lean_mk_string_unchecked(".", 1, 1);
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
x_1 = lean_mk_string_unchecked("> ", 2, 2);
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
x_3 = lean_array_to_list(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1(x_3, x_4);
x_6 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_7 = l_List_foldl___at_String_join___spec__1(x_6, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_array_to_list(x_9);
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
x_1 = lean_mk_string_unchecked("stderr:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_9 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_10 = lean_string_append(x_9, x_5);
x_11 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lake_logOutput___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
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
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lake_logOutput___rarg___closed__1;
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_apply_1(x_3, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_4);
return x_21;
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
x_1 = lean_mk_string_unchecked("failed to execute '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_rawProc___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_52; 
lean_inc(x_1);
x_52 = l_IO_Process_output(x_1, x_4);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_56);
x_5 = x_52;
x_6 = x_55;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
x_5 = x_60;
x_6 = x_58;
goto block_51;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_64);
x_5 = x_52;
x_6 = x_63;
goto block_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
x_5 = x_68;
x_6 = x_66;
goto block_51;
}
}
block_51:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lake_rawProc___lambda__1___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_rawProc___lambda__1___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_io_error_to_string(x_11);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_9);
x_24 = lean_array_push(x_9, x_22);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lake_rawProc___lambda__1___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lake_rawProc___lambda__1___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_io_error_to_string(x_27);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_26);
x_40 = lean_array_push(x_26, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_5, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_dec(x_5);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_6 = l_Lake_mkCmdLog(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_box(0);
x_11 = l_Lake_rawProc___lambda__1(x_1, x_10, x_9, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_5);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_box(0);
x_29 = l_Lake_rawProc___lambda__1(x_1, x_28, x_3, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
lean_ctor_set(x_30, 0, x_5);
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_43 = x_30;
} else {
 lean_dec_ref(x_30);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_rawProc___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_6);
x_12 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
if (x_2 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_push(x_4, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = 0;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_push(x_4, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
static lean_object* _init_l_Lake_proc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external command '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_proc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' exited with code ", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_5 = lean_array_get_size(x_3);
lean_inc(x_1);
x_96 = l_Lake_mkCmdLog(x_1);
x_97 = 0;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_push(x_3, x_98);
x_100 = lean_box(0);
lean_inc(x_1);
x_101 = l_Lake_rawProc___lambda__1(x_1, x_100, x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_6 = x_102;
x_7 = x_103;
goto block_95;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
lean_inc(x_5);
lean_ctor_set(x_102, 0, x_5);
x_6 = x_102;
x_7 = x_104;
goto block_95;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
lean_inc(x_5);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_5);
lean_ctor_set(x_108, 1, x_107);
x_6 = x_108;
x_7 = x_104;
goto block_95;
}
}
block_95:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_59 = lean_ctor_get(x_8, 0);
lean_inc(x_59);
x_60 = lean_string_utf8_byte_size(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_2 == 0)
{
uint8_t x_87; 
x_87 = 0;
x_63 = x_87;
goto block_86;
}
else
{
uint8_t x_88; 
x_88 = 1;
x_63 = x_88;
goto block_86;
}
block_58:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint32_t x_15; uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get_uint32(x_8, sizeof(void*)*2);
lean_dec(x_8);
x_16 = 0;
x_17 = lean_uint32_dec_eq(x_15, x_16);
x_18 = l_instDecidableNot___rarg(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lake_proc___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_proc___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_uint32_to_nat(x_15);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_push(x_13, x_32);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
lean_object* x_35; uint32_t x_36; uint32_t x_37; uint8_t x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get_uint32(x_8, sizeof(void*)*2);
lean_dec(x_8);
x_37 = 0;
x_38 = lean_uint32_dec_eq(x_36, x_37);
x_39 = l_instDecidableNot___rarg(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lake_proc___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lake_proc___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_uint32_to_nat(x_36);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_35, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_11);
return x_57;
}
}
}
block_86:
{
if (x_62 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = l_Lake_logOutput___rarg___closed__1;
x_65 = lean_string_append(x_64, x_59);
lean_dec(x_59);
x_66 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_67 = lean_string_append(x_65, x_66);
if (x_63 == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = 1;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_push(x_9, x_69);
x_71 = lean_box(0);
x_72 = l_Lake_proc___lambda__1(x_8, x_63, x_71, x_70, x_7);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_10 = x_73;
x_11 = x_74;
goto block_58;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = 0;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_push(x_9, x_76);
x_78 = lean_box(0);
x_79 = l_Lake_proc___lambda__1(x_8, x_63, x_78, x_77, x_7);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_10 = x_80;
x_11 = x_81;
goto block_58;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_59);
x_82 = lean_box(0);
x_83 = l_Lake_proc___lambda__1(x_8, x_63, x_82, x_9, x_7);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_10 = x_84;
x_11 = x_85;
goto block_58;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_6, 0);
lean_dec(x_90);
lean_ctor_set(x_6, 0, x_5);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_6);
lean_ctor_set(x_91, 1, x_7);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_6, 1);
lean_inc(x_92);
lean_dec(x_6);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_7);
return x_94;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lake_logOutput___rarg___lambda__1___closed__1;
x_10 = lean_string_append(x_9, x_5);
x_11 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_push(x_3, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_array_get_size(x_2);
x_195 = lean_box(0);
lean_inc(x_1);
x_196 = l_Lake_rawProc___lambda__1(x_1, x_195, x_2, x_3);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
lean_dec(x_194);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_4 = x_197;
x_5 = x_198;
goto block_193;
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
lean_ctor_set(x_197, 0, x_194);
x_4 = x_197;
x_5 = x_199;
goto block_193;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_202);
x_4 = x_203;
x_5 = x_199;
goto block_193;
}
}
block_193:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get_uint32(x_7, sizeof(void*)*2);
x_10 = 0;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_4);
lean_inc(x_1);
x_12 = l_Lake_mkCmdLog(x_1);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_get_size(x_8);
x_25 = lean_array_push(x_8, x_14);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_30 = l_Lake_logOutput___rarg___closed__1;
x_31 = lean_string_append(x_30, x_26);
lean_dec(x_26);
x_32 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_25, x_35);
x_37 = lean_box(0);
x_38 = l_Lake_captureProc___lambda__1(x_7, x_37, x_36, x_5);
lean_dec(x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lake_proc___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_proc___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_uint32_to_nat(x_9);
x_50 = l___private_Init_Data_Repr_0__Nat_reprFast(x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_string_append(x_51, x_32);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_42, x_54);
lean_ctor_set(x_39, 1, x_55);
lean_ctor_set(x_39, 0, x_37);
x_16 = x_39;
x_17 = x_40;
goto block_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_dec(x_39);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l_Lake_proc___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lake_proc___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_uint32_to_nat(x_9);
x_63 = l___private_Init_Data_Repr_0__Nat_reprFast(x_62);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
x_65 = lean_string_append(x_64, x_32);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_56, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_37);
lean_ctor_set(x_69, 1, x_68);
x_16 = x_69;
x_17 = x_40;
goto block_24;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_26);
x_70 = lean_box(0);
x_71 = l_Lake_captureProc___lambda__1(x_7, x_70, x_25, x_5);
lean_dec(x_7);
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
x_82 = lean_uint32_to_nat(x_9);
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
lean_ctor_set(x_72, 0, x_70);
x_16 = x_72;
x_17 = x_73;
goto block_24;
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
x_96 = lean_uint32_to_nat(x_9);
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
lean_ctor_set(x_104, 0, x_70);
lean_ctor_set(x_104, 1, x_103);
x_16 = x_104;
x_17 = x_73;
goto block_24;
}
}
block_24:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_105 = lean_ctor_get(x_7, 0);
lean_inc(x_105);
lean_dec(x_7);
x_106 = lean_string_utf8_byte_size(x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_105, x_106, x_107);
x_109 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_105, x_108, x_106);
x_110 = lean_string_utf8_extract(x_105, x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_105);
lean_ctor_set(x_4, 0, x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_4);
lean_ctor_set(x_111, 1, x_5);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint32_t x_114; uint32_t x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_4, 0);
x_113 = lean_ctor_get(x_4, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_4);
x_114 = lean_ctor_get_uint32(x_112, sizeof(void*)*2);
x_115 = 0;
x_116 = lean_uint32_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_inc(x_1);
x_117 = l_Lake_mkCmdLog(x_1);
x_118 = 0;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_get_size(x_113);
x_128 = lean_array_push(x_113, x_119);
x_129 = lean_ctor_get(x_112, 0);
lean_inc(x_129);
x_130 = lean_string_utf8_byte_size(x_129);
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_nat_dec_eq(x_130, x_131);
lean_dec(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_133 = l_Lake_logOutput___rarg___closed__1;
x_134 = lean_string_append(x_133, x_129);
lean_dec(x_129);
x_135 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_136 = lean_string_append(x_134, x_135);
x_137 = 1;
x_138 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_137);
x_139 = lean_array_push(x_128, x_138);
x_140 = lean_box(0);
x_141 = l_Lake_captureProc___lambda__1(x_112, x_140, x_139, x_5);
lean_dec(x_112);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
lean_dec(x_1);
x_147 = l_Lake_proc___closed__1;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = l_Lake_proc___closed__2;
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_uint32_to_nat(x_114);
x_152 = l___private_Init_Data_Repr_0__Nat_reprFast(x_151);
x_153 = lean_string_append(x_150, x_152);
lean_dec(x_152);
x_154 = lean_string_append(x_153, x_135);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_array_push(x_144, x_156);
if (lean_is_scalar(x_145)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_145;
}
lean_ctor_set(x_158, 0, x_140);
lean_ctor_set(x_158, 1, x_157);
x_121 = x_158;
x_122 = x_143;
goto block_127;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_129);
x_159 = lean_box(0);
x_160 = l_Lake_captureProc___lambda__1(x_112, x_159, x_128, x_5);
lean_dec(x_112);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_1, 1);
lean_inc(x_165);
lean_dec(x_1);
x_166 = l_Lake_proc___closed__1;
x_167 = lean_string_append(x_166, x_165);
lean_dec(x_165);
x_168 = l_Lake_proc___closed__2;
x_169 = lean_string_append(x_167, x_168);
x_170 = lean_uint32_to_nat(x_114);
x_171 = l___private_Init_Data_Repr_0__Nat_reprFast(x_170);
x_172 = lean_string_append(x_169, x_171);
lean_dec(x_171);
x_173 = l_List_mapTR_loop___at_Lake_mkCmdLog___spec__1___closed__2;
x_174 = lean_string_append(x_172, x_173);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_array_push(x_163, x_176);
if (lean_is_scalar(x_164)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_164;
}
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_177);
x_121 = x_178;
x_122 = x_162;
goto block_127;
}
block_127:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_1);
x_179 = lean_ctor_get(x_112, 0);
lean_inc(x_179);
lean_dec(x_112);
x_180 = lean_string_utf8_byte_size(x_179);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_179, x_180, x_181);
x_183 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_179, x_182, x_180);
x_184 = lean_string_utf8_extract(x_179, x_182, x_183);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_179);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_113);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_5);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_4);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_4);
lean_ctor_set(x_188, 1, x_5);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_4, 0);
x_190 = lean_ctor_get(x_4, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_4);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_5);
return x_192;
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_10, x_11, x_12);
x_14 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_10, x_13, x_11);
x_15 = lean_string_utf8_extract(x_10, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; uint32_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get_uint32(x_17, sizeof(void*)*2);
x_20 = 0;
x_21 = lean_uint32_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_string_utf8_byte_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_24, x_25, x_26);
x_28 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_24, x_27, x_25);
x_29 = lean_string_utf8_extract(x_24, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_3, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_34);
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
static lean_object* _init_l_Lake_testProc___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_testProc(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = l_Lake_testProc___closed__1;
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_process_child_wait(x_5, x_7, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = 0;
x_13 = lean_unbox_uint32(x_11);
lean_dec(x_11);
x_14 = lean_uint32_dec_eq(x_13, x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = 0;
x_19 = lean_unbox_uint32(x_16);
lean_dec(x_16);
x_20 = lean_uint32_dec_eq(x_19, x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_ctor_get(x_1, 4);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_44 = l_Lake_testProc___closed__1;
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_43);
x_46 = lean_io_process_spawn(x_45, x_2);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_io_process_child_wait(x_44, x_47, x_48);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; uint32_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = 0;
x_54 = lean_unbox_uint32(x_50);
lean_dec(x_50);
x_55 = lean_uint32_dec_eq(x_54, x_53);
x_56 = lean_box(x_55);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_59 = x_49;
} else {
 lean_dec_ref(x_49);
 x_59 = lean_box(0);
}
x_60 = 0;
x_61 = lean_box(x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_64 = x_46;
} else {
 lean_dec_ref(x_46);
 x_64 = lean_box(0);
}
x_65 = 0;
x_66 = lean_box(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
 lean_ctor_set_tag(x_67, 0);
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
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
l_Lake_testProc___closed__1 = _init_l_Lake_testProc___closed__1();
lean_mark_persistent(l_Lake_testProc___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
