// Lean compiler output
// Module: Lake.Util.Proc
// Imports: public import Lake.Util.Log import Init.Data.String.TakeDrop
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
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4;
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_proc___closed__0;
static lean_object* l_Lake_proc___closed__1;
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0;
static lean_object* l_Lake_logOutput___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__0;
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_testProc___closed__0;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lake_logOutput___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_rawProc___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1;
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object*);
static lean_object* l_Lake_mkCmdLog___closed__1;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_proc_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lake_logOutput___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_proc_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_rawProc___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_proc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH ", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0;
x_14 = lean_string_dec_eq(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1;
x_16 = lean_string_append(x_11, x_15);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; 
x_22 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3;
x_17 = x_22;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec_ref(x_12);
x_17 = x_23;
goto block_21;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_7 = x_20;
goto block_10;
}
}
else
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
x_24 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4;
x_7 = x_24;
goto block_10;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lake_mkCmdLog___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("> ", 2, 2);
return x_1;
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
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_array_to_list(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(x_6, x_7);
x_9 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3;
x_10 = l_List_foldl___at___Lake_mkCmdLog_spec__1(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2;
x_12 = lean_array_to_list(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_String_intercalate(x_11, x_13);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; 
x_21 = l_Lake_mkCmdLog___closed__1;
x_15 = x_21;
goto block_20;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec_ref(x_4);
x_15 = x_22;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lake_mkCmdLog___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_10);
lean_dec_ref(x_10);
x_19 = lean_string_append(x_18, x_14);
lean_dec_ref(x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___Lake_mkCmdLog_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_logOutput___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderr:\n", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_logOutput___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_3);
x_8 = l_Lake_logOutput___redArg___lam__0___closed__0;
x_9 = l_Lake_logOutput___redArg___lam__0___closed__1;
x_10 = l_Substring_takeWhileAux(x_1, x_5, x_9, x_6);
x_11 = l_Substring_takeRightWhileAux(x_1, x_10, x_9, x_5);
x_12 = lean_string_utf8_extract(x_1, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_string_append(x_8, x_12);
lean_dec_ref(x_12);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_logOutput___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_1);
x_7 = lean_string_utf8_byte_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_6);
x_12 = l_Lake_logOutput___redArg___closed__0;
x_13 = l_Lake_logOutput___redArg___lam__0___closed__1;
x_14 = l_Substring_takeWhileAux(x_4, x_7, x_13, x_8);
x_15 = l_Substring_takeRightWhileAux(x_4, x_14, x_13, x_7);
x_16 = lean_string_utf8_extract(x_4, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
x_17 = lean_string_append(x_12, x_16);
lean_dec_ref(x_16);
x_18 = lean_apply_1(x_3, x_17);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_18, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_23, 0, x_6);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_22, lean_box(0), x_24);
x_26 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_25, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_string_utf8_byte_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_7);
x_13 = l_Lake_logOutput___redArg___closed__0;
x_14 = l_Lake_logOutput___redArg___lam__0___closed__1;
x_15 = l_Substring_takeWhileAux(x_5, x_8, x_14, x_9);
x_16 = l_Substring_takeRightWhileAux(x_5, x_15, x_14, x_8);
x_17 = lean_string_utf8_extract(x_5, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_5);
x_18 = lean_string_append(x_13, x_17);
lean_dec_ref(x_17);
x_19 = lean_apply_1(x_4, x_18);
x_20 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_19, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_24, 0, x_7);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_23, lean_box(0), x_25);
x_27 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_26, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logOutput___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_rawProc___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to execute '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_rawProc___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc_ref(x_1);
x_6 = l_IO_Process_output(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = l_Lake_rawProc___lam__0___closed__0;
x_12 = lean_string_append(x_11, x_10);
lean_dec_ref(x_10);
x_13 = l_Lake_rawProc___lam__0___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_io_error_to_string(x_9);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_3);
x_20 = lean_array_push(x_3, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_3);
if (x_2 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_1);
x_12 = l_Lake_mkCmdLog(x_1);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_box(0);
x_16 = lean_array_push(x_3, x_14);
x_17 = l_Lake_rawProc___lam__0(x_1, x_15, x_16);
x_6 = x_17;
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lake_rawProc___lam__0(x_1, x_18, x_3);
x_6 = x_19;
goto block_11;
}
block_11:
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_rawProc___lam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_rawProc(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_proc_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = 1;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_box(0);
x_9 = lean_array_push(x_4, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_2);
x_12 = lean_box(0);
x_13 = lean_array_push(x_4, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lake_logOutput___redArg___lam__0___closed__0;
x_10 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_1, x_6, x_7);
x_11 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_1, x_10, x_6);
x_12 = lean_string_utf8_extract(x_1, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = lean_apply_3(x_2, x_13, x_4, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
}
static lean_object* _init_l_Lake_proc___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external command '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_proc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' exited with code ", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_array_get_size(x_3);
lean_inc_ref(x_1);
x_10 = l_Lake_mkCmdLog(x_1);
x_11 = 0;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_box(0);
lean_inc_ref(x_1);
x_15 = l_IO_Process_output(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get_uint32(x_16, sizeof(void*)*2);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
lean_dec(x_16);
x_58 = lean_box(x_2);
x_59 = lean_box(x_11);
x_60 = lean_alloc_closure((void*)(l_Lake_proc___lam__0___boxed), 5, 2);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_59);
x_61 = lean_string_utf8_byte_size(x_18);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = l_Lake_logOutput___redArg___closed__0;
x_65 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_18, x_61, x_62);
x_66 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_18, x_65, x_61);
x_67 = lean_string_utf8_extract(x_18, x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_18);
x_68 = lean_string_append(x_64, x_67);
lean_dec_ref(x_67);
x_69 = l_Lake_proc___lam__0(x_2, x_11, x_68, x_13);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lake_proc___lam__1(x_19, x_60, x_70, x_71);
lean_dec_ref(x_19);
x_20 = x_72;
goto block_57;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
lean_dec_ref(x_18);
x_73 = lean_box(0);
x_74 = l_Lake_proc___lam__1(x_19, x_60, x_73, x_13);
lean_dec_ref(x_19);
x_20 = x_74;
goto block_57;
}
block_57:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_uint32_dec_eq(x_17, x_24);
x_26 = l_instDecidableNot___redArg(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_20);
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = l_Lake_proc___closed__0;
x_30 = lean_string_append(x_29, x_28);
lean_dec_ref(x_28);
x_31 = l_Lake_proc___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_uint32_to_nat(x_17);
x_34 = l_Nat_reprFast(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_push(x_22, x_37);
x_6 = x_38;
x_7 = lean_box(0);
goto block_9;
}
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = 0;
x_41 = lean_uint32_dec_eq(x_17, x_40);
x_42 = l_instDecidableNot___redArg(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_1);
x_46 = l_Lake_proc___closed__0;
x_47 = lean_string_append(x_46, x_45);
lean_dec_ref(x_45);
x_48 = l_Lake_proc___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_uint32_to_nat(x_17);
x_51 = l_Nat_reprFast(x_50);
x_52 = lean_string_append(x_49, x_51);
lean_dec_ref(x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_39, x_54);
x_6 = x_55;
x_7 = lean_box(0);
goto block_9;
}
}
}
else
{
lean_object* x_56; 
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_dec_ref(x_20);
x_6 = x_56;
x_7 = lean_box(0);
goto block_9;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_15, 0);
lean_inc(x_75);
lean_dec_ref(x_15);
x_76 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_76);
lean_dec_ref(x_1);
x_77 = l_Lake_rawProc___lam__0___closed__0;
x_78 = lean_string_append(x_77, x_76);
lean_dec_ref(x_76);
x_79 = l_Lake_rawProc___lam__0___closed__1;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_io_error_to_string(x_75);
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_push(x_13, x_84);
x_6 = x_85;
x_7 = lean_box(0);
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_proc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_proc_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_Lake_proc___lam__0(x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_proc___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_proc(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lake_logOutput___redArg___lam__0___closed__0;
x_9 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_1, x_5, x_6);
x_10 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_1, x_9, x_5);
x_11 = lean_string_utf8_extract(x_1, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_string_append(x_8, x_11);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_box(0);
x_16 = lean_array_push(x_3, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
lean_inc_ref(x_1);
x_5 = l_IO_Process_output(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get_uint32(x_6, sizeof(void*)*2);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = 0;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_20; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_dec(x_6);
lean_inc_ref(x_1);
x_12 = l_Lake_mkCmdLog(x_1);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_get_size(x_2);
x_34 = lean_array_push(x_2, x_14);
x_35 = lean_string_utf8_byte_size(x_8);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = l_Lake_logOutput___redArg___closed__0;
x_39 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_8, x_35, x_36);
x_40 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_8, x_39, x_35);
x_41 = lean_string_utf8_extract(x_8, x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_8);
x_42 = lean_string_append(x_38, x_41);
lean_dec_ref(x_41);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_box(0);
x_46 = lean_array_push(x_34, x_44);
x_47 = l_Lake_captureProc_x27___lam__0(x_9, x_45, x_46);
lean_dec_ref(x_9);
x_20 = x_47;
goto block_33;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
lean_dec_ref(x_8);
x_48 = lean_box(0);
x_49 = l_Lake_captureProc_x27___lam__0(x_9, x_48, x_34);
lean_dec_ref(x_9);
x_20 = x_49;
goto block_33;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_33:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = l_Lake_proc___closed__0;
x_24 = lean_string_append(x_23, x_22);
lean_dec_ref(x_22);
x_25 = l_Lake_proc___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_uint32_to_nat(x_7);
x_28 = l_Nat_reprFast(x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_21, x_31);
x_16 = x_32;
x_17 = lean_box(0);
goto block_19;
}
}
else
{
lean_object* x_50; 
lean_dec_ref(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_2);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
lean_dec_ref(x_5);
x_52 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_array_get_size(x_2);
x_54 = l_Lake_rawProc___lam__0___closed__0;
x_55 = lean_string_append(x_54, x_52);
lean_dec_ref(x_52);
x_56 = l_Lake_rawProc___lam__0___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_io_error_to_string(x_51);
x_59 = lean_string_append(x_57, x_58);
lean_dec_ref(x_58);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_push(x_2, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_captureProc_x27___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_captureProc_x27(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_captureProc_x27(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = l_Lake_logOutput___redArg___lam__0___closed__1;
x_11 = l_Substring_takeWhileAux(x_7, x_9, x_10, x_8);
x_12 = l_Substring_takeRightWhileAux(x_7, x_11, x_10, x_9);
x_13 = lean_string_utf8_extract(x_7, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_string_utf8_byte_size(x_16);
x_19 = l_Lake_logOutput___redArg___lam__0___closed__1;
x_20 = l_Substring_takeWhileAux(x_16, x_18, x_19, x_17);
x_21 = l_Substring_takeRightWhileAux(x_16, x_20, x_19, x_18);
x_22 = lean_string_utf8_extract(x_16, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_captureProc(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_IO_Process_output(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get_uint32(x_6, sizeof(void*)*2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = 0;
x_10 = lean_uint32_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_dec_ref(x_8);
lean_free_object(x_4);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_8);
x_13 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_8, x_12, x_11);
x_14 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_8, x_13, x_12);
x_15 = lean_string_utf8_extract(x_8, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_8);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; uint32_t x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get_uint32(x_16, sizeof(void*)*2);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = lean_uint32_dec_eq(x_17, x_19);
if (x_20 == 0)
{
lean_dec_ref(x_18);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_byte_size(x_18);
x_23 = l_Substring_takeWhileAux___at___Lake_proc_spec__0(x_18, x_22, x_21);
x_24 = l_Substring_takeRightWhileAux___at___Lake_proc_spec__1(x_18, x_23, x_22);
x_25 = lean_string_utf8_extract(x_18, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_dec_ref(x_4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_captureProc_x3f(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_testProc___closed__0() {
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
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_Lake_testProc___closed__0;
lean_ctor_set(x_1, 0, x_8);
x_9 = lean_io_process_spawn(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_io_process_child_wait(x_8, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 0;
x_14 = lean_unbox_uint32(x_12);
lean_dec(x_12);
x_15 = lean_uint32_dec_eq(x_14, x_13);
return x_15;
}
else
{
lean_dec_ref(x_11);
x_3 = lean_box(0);
goto block_5;
}
}
else
{
lean_dec_ref(x_9);
x_3 = lean_box(0);
goto block_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_22 = l_Lake_testProc___closed__0;
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_21);
x_24 = lean_io_process_spawn(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_io_process_child_wait(x_22, x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 0;
x_29 = lean_unbox_uint32(x_27);
lean_dec(x_27);
x_30 = lean_uint32_dec_eq(x_29, x_28);
return x_30;
}
else
{
lean_dec_ref(x_26);
x_3 = lean_box(0);
goto block_5;
}
}
else
{
lean_dec_ref(x_24);
x_3 = lean_box(0);
goto block_5;
}
}
block_5:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_testProc(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Proc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0 = _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__0);
l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1 = _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__1);
l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2 = _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__2);
l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3 = _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__3);
l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4 = _init_l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0___closed__4);
l_Lake_mkCmdLog___closed__0 = _init_l_Lake_mkCmdLog___closed__0();
lean_mark_persistent(l_Lake_mkCmdLog___closed__0);
l_Lake_mkCmdLog___closed__1 = _init_l_Lake_mkCmdLog___closed__1();
lean_mark_persistent(l_Lake_mkCmdLog___closed__1);
l_Lake_logOutput___redArg___lam__0___closed__0 = _init_l_Lake_logOutput___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lake_logOutput___redArg___lam__0___closed__0);
l_Lake_logOutput___redArg___lam__0___closed__1 = _init_l_Lake_logOutput___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lake_logOutput___redArg___lam__0___closed__1);
l_Lake_logOutput___redArg___closed__0 = _init_l_Lake_logOutput___redArg___closed__0();
lean_mark_persistent(l_Lake_logOutput___redArg___closed__0);
l_Lake_rawProc___lam__0___closed__0 = _init_l_Lake_rawProc___lam__0___closed__0();
lean_mark_persistent(l_Lake_rawProc___lam__0___closed__0);
l_Lake_rawProc___lam__0___closed__1 = _init_l_Lake_rawProc___lam__0___closed__1();
lean_mark_persistent(l_Lake_rawProc___lam__0___closed__1);
l_Lake_proc___closed__0 = _init_l_Lake_proc___closed__0();
lean_mark_persistent(l_Lake_proc___closed__0);
l_Lake_proc___closed__1 = _init_l_Lake_proc___closed__1();
lean_mark_persistent(l_Lake_proc___closed__1);
l_Lake_testProc___closed__0 = _init_l_Lake_testProc___closed__0();
lean_mark_persistent(l_Lake_testProc___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
