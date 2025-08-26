// Lean compiler output
// Module: Lake.Util.Cli
// Imports: Init.Control.State Init.Data.Array.Basic
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
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_processOptions___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_shortOptionWithSpace___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ArgList_mk(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_ArgsT_run_x27___redArg___lam__0___boxed), 1, 0);
x_6 = lean_apply_1(x_3, x_2);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_ArgsT_run_x27___redArg___lam__0___boxed), 1, 0);
x_8 = lean_apply_1(x_5, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ArgsT_run_x27___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getArgs___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getArgs(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_takeArg_x3f___redArg___lam__0), 1, 0);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_takeArg_x3f___redArg___lam__0), 1, 0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_ctor_set_tag(x_2, 0);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_takeArgs___redArg___lam__0), 1, 0);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_takeArgs___redArg___lam__0), 1, 0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_string_utf8_get(x_1, x_4);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_3);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_4);
lean_inc(x_13);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_4);
x_14 = l_Substring_nextn(x_2, x_11, x_12);
lean_dec_ref(x_2);
x_15 = lean_string_utf8_extract(x_4, x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
lean_dec_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_2(x_7, lean_box(0), x_16);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
lean_inc_ref(x_4);
x_20 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_3);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_string_utf8_byte_size(x_4);
lean_inc(x_23);
lean_inc_ref(x_4);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Substring_nextn(x_24, x_21, x_22);
lean_dec_ref(x_24);
x_26 = lean_string_utf8_extract(x_4, x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
lean_dec_ref(x_4);
x_27 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_apply_2(x_19, lean_box(0), x_27);
x_29 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_28, x_20);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_6);
lean_inc(x_15);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_6);
x_16 = l_Substring_nextn(x_3, x_13, x_14);
lean_dec_ref(x_3);
x_17 = lean_string_utf8_extract(x_6, x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
lean_dec_ref(x_6);
x_18 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
lean_inc_ref(x_6);
x_22 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_5);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_string_utf8_byte_size(x_6);
lean_inc(x_25);
lean_inc_ref(x_6);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Substring_nextn(x_26, x_23, x_24);
lean_dec_ref(x_26);
x_28 = lean_string_utf8_extract(x_6, x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
lean_dec_ref(x_6);
x_29 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_apply_2(x_21, lean_box(0), x_29);
x_31 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_30, x_22);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_shortOptionWithEq___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_shortOptionWithSpace___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_3);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_4);
lean_inc(x_13);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_4);
x_14 = l_Substring_nextn(x_2, x_11, x_12);
lean_dec_ref(x_2);
x_15 = lean_string_utf8_extract(x_4, x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
lean_dec_ref(x_4);
x_16 = lean_string_utf8_byte_size(x_15);
x_17 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_18 = l_Substring_takeWhileAux(x_15, x_16, x_17, x_12);
x_19 = lean_string_utf8_extract(x_15, x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
lean_dec_ref(x_15);
x_20 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_apply_2(x_7, lean_box(0), x_20);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_21, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
lean_inc_ref(x_4);
x_24 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_24, 0, x_4);
lean_closure_set(x_24, 1, x_3);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_byte_size(x_4);
lean_inc(x_27);
lean_inc_ref(x_4);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Substring_nextn(x_28, x_25, x_26);
lean_dec_ref(x_28);
x_30 = lean_string_utf8_extract(x_4, x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
lean_dec_ref(x_4);
x_31 = lean_string_utf8_byte_size(x_30);
x_32 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_33 = l_Substring_takeWhileAux(x_30, x_31, x_32, x_26);
x_34 = lean_string_utf8_extract(x_30, x_33, x_31);
lean_dec(x_31);
lean_dec(x_33);
lean_dec_ref(x_30);
x_35 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_apply_2(x_23, lean_box(0), x_35);
x_37 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_36, x_24);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_6);
lean_inc(x_15);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_6);
x_16 = l_Substring_nextn(x_3, x_13, x_14);
lean_dec_ref(x_3);
x_17 = lean_string_utf8_extract(x_6, x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
lean_dec_ref(x_6);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_20 = l_Substring_takeWhileAux(x_17, x_18, x_19, x_14);
x_21 = lean_string_utf8_extract(x_17, x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_dec_ref(x_17);
x_22 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_apply_2(x_9, lean_box(0), x_22);
x_24 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_23, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
lean_inc_ref(x_6);
x_26 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_6);
lean_closure_set(x_26, 1, x_5);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_string_utf8_byte_size(x_6);
lean_inc(x_29);
lean_inc_ref(x_6);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Substring_nextn(x_30, x_27, x_28);
lean_dec_ref(x_30);
x_32 = lean_string_utf8_extract(x_6, x_31, x_29);
lean_dec(x_29);
lean_dec(x_31);
lean_dec_ref(x_6);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_35 = l_Substring_takeWhileAux(x_32, x_33, x_34, x_28);
x_36 = lean_string_utf8_extract(x_32, x_35, x_33);
lean_dec(x_33);
lean_dec(x_35);
lean_dec_ref(x_32);
x_37 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_apply_2(x_25, lean_box(0), x_37);
x_39 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_38, x_26);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_inc_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_3);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_4);
lean_inc(x_13);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_4);
x_14 = l_Substring_nextn(x_2, x_11, x_12);
lean_dec_ref(x_2);
x_15 = lean_string_utf8_extract(x_4, x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
lean_dec_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_2(x_7, lean_box(0), x_16);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
lean_inc_ref(x_4);
x_20 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_3);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_string_utf8_byte_size(x_4);
lean_inc(x_23);
lean_inc_ref(x_4);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Substring_nextn(x_24, x_21, x_22);
lean_dec_ref(x_24);
x_26 = lean_string_utf8_extract(x_4, x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
lean_dec_ref(x_4);
x_27 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_apply_2(x_19, lean_box(0), x_27);
x_29 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_28, x_20);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_6);
lean_inc(x_15);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_6);
x_16 = l_Substring_nextn(x_3, x_13, x_14);
lean_dec_ref(x_3);
x_17 = lean_string_utf8_extract(x_6, x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
lean_dec_ref(x_6);
x_18 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
lean_inc_ref(x_6);
x_22 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_5);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_string_utf8_byte_size(x_6);
lean_inc(x_25);
lean_inc_ref(x_6);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Substring_nextn(x_26, x_23, x_24);
lean_dec_ref(x_26);
x_28 = lean_string_utf8_extract(x_6, x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
lean_dec_ref(x_6);
x_29 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_apply_2(x_21, lean_box(0), x_29);
x_31 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_30, x_22);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_next_fast(x_1, x_2);
x_7 = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(x_3, x_4, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_2);
x_8 = lean_string_utf8_get_fast(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_box_uint32(x_8);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = 32;
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_posOfAux(x_4, x_5, x_6, x_7);
x_9 = lean_nat_dec_eq(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_3);
x_13 = lean_string_utf8_next(x_4, x_8);
lean_dec(x_8);
x_14 = lean_string_utf8_extract(x_4, x_13, x_6);
lean_dec(x_6);
lean_dec(x_13);
lean_dec_ref(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_apply_2(x_11, lean_box(0), x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_12);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_3, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 32;
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_String_posOfAux(x_6, x_7, x_8, x_9);
x_11 = lean_nat_dec_eq(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_dec_ref(x_3);
lean_inc(x_10);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_5);
x_15 = lean_string_utf8_next(x_6, x_10);
lean_dec(x_10);
x_16 = lean_string_utf8_extract(x_6, x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
lean_dec_ref(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
x_19 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_18, x_14);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_apply_1(x_5, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_longOptionOrSpace___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = 61;
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_posOfAux(x_4, x_5, x_6, x_7);
x_9 = lean_nat_dec_eq(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_3);
x_13 = lean_string_utf8_next(x_4, x_8);
lean_dec(x_8);
x_14 = lean_string_utf8_extract(x_4, x_13, x_6);
lean_dec(x_6);
lean_dec(x_13);
lean_dec_ref(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_apply_2(x_11, lean_box(0), x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_12);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_3, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 61;
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_String_posOfAux(x_6, x_7, x_8, x_9);
x_11 = lean_nat_dec_eq(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_dec_ref(x_3);
lean_inc(x_10);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_5);
x_15 = lean_string_utf8_next(x_6, x_10);
lean_dec(x_10);
x_16 = lean_string_utf8_extract(x_6, x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
lean_dec_ref(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
x_19 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_18, x_14);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_apply_1(x_5, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_string_utf8_extract(x_1, x_2, x_3);
x_9 = 32;
x_10 = lean_string_utf8_byte_size(x_8);
lean_inc(x_2);
x_11 = l_String_posOfAux(x_8, x_9, x_10, x_2);
x_12 = lean_nat_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_11);
lean_inc_ref(x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_string_utf8_next(x_8, x_11);
lean_dec(x_11);
x_15 = lean_string_utf8_extract(x_8, x_14, x_10);
lean_dec(x_10);
lean_dec(x_14);
lean_dec_ref(x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_2(x_5, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_apply_1(x_4, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = 61;
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_posOfAux(x_4, x_5, x_6, x_7);
x_9 = lean_nat_dec_eq(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc(x_10);
lean_inc(x_11);
lean_inc(x_8);
lean_inc_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_10);
x_13 = lean_string_utf8_next(x_4, x_8);
lean_dec(x_8);
x_14 = lean_string_utf8_extract(x_4, x_13, x_6);
lean_dec(x_6);
lean_dec(x_13);
lean_dec_ref(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_apply_2(x_11, lean_box(0), x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_12);
return x_17;
}
else
{
uint32_t x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
x_18 = 32;
x_19 = l_String_posOfAux(x_4, x_18, x_6, x_7);
x_20 = lean_nat_dec_eq(x_19, x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec_ref(x_2);
lean_inc(x_19);
lean_inc_ref(x_4);
x_23 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_7);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_3);
x_24 = lean_string_utf8_next(x_4, x_19);
lean_dec(x_19);
x_25 = lean_string_utf8_extract(x_4, x_24, x_6);
lean_dec(x_6);
lean_dec(x_24);
lean_dec_ref(x_4);
x_26 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_apply_2(x_22, lean_box(0), x_26);
x_28 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_27, x_23);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_apply_1(x_3, x_4);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 61;
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_String_posOfAux(x_6, x_7, x_8, x_9);
x_11 = lean_nat_dec_eq(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_dec_ref(x_3);
lean_inc(x_12);
lean_inc(x_13);
lean_inc(x_10);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_string_utf8_next(x_6, x_10);
lean_dec(x_10);
x_16 = lean_string_utf8_extract(x_6, x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
lean_dec_ref(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
x_19 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_18, x_14);
return x_19;
}
else
{
uint32_t x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_10);
x_20 = 32;
x_21 = l_String_posOfAux(x_6, x_20, x_8, x_9);
x_22 = lean_nat_dec_eq(x_21, x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
lean_dec_ref(x_3);
lean_inc(x_21);
lean_inc_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_9);
lean_closure_set(x_25, 2, x_21);
lean_closure_set(x_25, 3, x_5);
x_26 = lean_string_utf8_next(x_6, x_21);
lean_dec(x_21);
x_27 = lean_string_utf8_extract(x_6, x_26, x_8);
lean_dec(x_8);
lean_dec(x_26);
lean_dec_ref(x_6);
x_28 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_apply_2(x_24, lean_box(0), x_28);
x_30 = lean_apply_4(x_23, lean_box(0), lean_box(0), x_29, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_apply_1(x_5, x_6);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_longOption___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_longOption___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_string_utf8_get(x_1, x_4);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get(x_5, x_7);
x_10 = 61;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 32;
x_13 = lean_uint32_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
lean_inc_ref(x_5);
x_20 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_byte_size(x_5);
lean_inc(x_22);
lean_inc_ref(x_5);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_5);
x_23 = l_Substring_nextn(x_2, x_7, x_21);
lean_dec_ref(x_2);
x_24 = lean_string_utf8_extract(x_5, x_23, x_22);
lean_dec(x_22);
lean_dec(x_23);
lean_dec_ref(x_5);
x_25 = lean_string_utf8_byte_size(x_24);
x_26 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_27 = l_Substring_takeWhileAux(x_24, x_25, x_26, x_21);
x_28 = lean_string_utf8_extract(x_24, x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
lean_dec_ref(x_24);
x_29 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_apply_2(x_17, lean_box(0), x_29);
x_31 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_30, x_20);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_dec(x_2);
lean_inc_ref(x_5);
x_33 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_33, 0, x_5);
lean_closure_set(x_33, 1, x_3);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_utf8_byte_size(x_5);
lean_inc(x_35);
lean_inc_ref(x_5);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Substring_nextn(x_36, x_7, x_34);
lean_dec_ref(x_36);
x_38 = lean_string_utf8_extract(x_5, x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
lean_dec_ref(x_5);
x_39 = lean_string_utf8_byte_size(x_38);
x_40 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_41 = l_Substring_takeWhileAux(x_38, x_39, x_40, x_34);
x_42 = lean_string_utf8_extract(x_38, x_41, x_39);
lean_dec(x_39);
lean_dec(x_41);
lean_dec_ref(x_38);
x_43 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_apply_2(x_32, lean_box(0), x_43);
x_45 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_44, x_33);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_4);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
lean_inc_ref(x_5);
x_51 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_51, 0, x_5);
lean_closure_set(x_51, 1, x_3);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_string_utf8_byte_size(x_5);
lean_inc(x_54);
lean_inc_ref(x_5);
lean_ctor_set(x_2, 2, x_54);
lean_ctor_set(x_2, 1, x_53);
lean_ctor_set(x_2, 0, x_5);
x_55 = l_Substring_nextn(x_2, x_52, x_53);
lean_dec_ref(x_2);
x_56 = lean_string_utf8_extract(x_5, x_55, x_54);
lean_dec(x_54);
lean_dec(x_55);
lean_dec_ref(x_5);
x_57 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_apply_2(x_48, lean_box(0), x_57);
x_59 = lean_apply_4(x_46, lean_box(0), lean_box(0), x_58, x_51);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_dec(x_2);
lean_inc_ref(x_5);
x_61 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_61, 0, x_5);
lean_closure_set(x_61, 1, x_3);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_string_utf8_byte_size(x_5);
lean_inc(x_64);
lean_inc_ref(x_5);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Substring_nextn(x_65, x_62, x_63);
lean_dec_ref(x_65);
x_67 = lean_string_utf8_extract(x_5, x_66, x_64);
lean_dec(x_64);
lean_dec(x_66);
lean_dec_ref(x_5);
x_68 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_apply_2(x_60, lean_box(0), x_68);
x_70 = lean_apply_4(x_46, lean_box(0), lean_box(0), x_69, x_61);
return x_70;
}
}
}
else
{
lean_object* x_71; uint32_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_string_utf8_get(x_5, x_71);
lean_dec_ref(x_5);
x_73 = lean_box_uint32(x_72);
x_74 = lean_apply_1(x_3, x_73);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_length(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_7, x_9);
x_12 = 61;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 32;
x_15 = lean_uint32_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_apply_1(x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
lean_inc_ref(x_7);
x_22 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_22, 0, x_7);
lean_closure_set(x_22, 1, x_5);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_string_utf8_byte_size(x_7);
lean_inc(x_24);
lean_inc_ref(x_7);
lean_ctor_set(x_3, 2, x_24);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_7);
x_25 = l_Substring_nextn(x_3, x_9, x_23);
lean_dec_ref(x_3);
x_26 = lean_string_utf8_extract(x_7, x_25, x_24);
lean_dec(x_24);
lean_dec(x_25);
lean_dec_ref(x_7);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_29 = l_Substring_takeWhileAux(x_26, x_27, x_28, x_23);
x_30 = lean_string_utf8_extract(x_26, x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
lean_dec_ref(x_26);
x_31 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_apply_2(x_19, lean_box(0), x_31);
x_33 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_32, x_22);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
lean_dec(x_3);
lean_inc_ref(x_7);
x_35 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_35, 0, x_7);
lean_closure_set(x_35, 1, x_5);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_utf8_byte_size(x_7);
lean_inc(x_37);
lean_inc_ref(x_7);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Substring_nextn(x_38, x_9, x_36);
lean_dec_ref(x_38);
x_40 = lean_string_utf8_extract(x_7, x_39, x_37);
lean_dec(x_37);
lean_dec(x_39);
lean_dec_ref(x_7);
x_41 = lean_string_utf8_byte_size(x_40);
x_42 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_43 = l_Substring_takeWhileAux(x_40, x_41, x_42, x_36);
x_44 = lean_string_utf8_extract(x_40, x_43, x_41);
lean_dec(x_41);
lean_dec(x_43);
lean_dec_ref(x_40);
x_45 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_apply_2(x_34, lean_box(0), x_45);
x_47 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_46, x_35);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_6);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_3, 2);
x_51 = lean_ctor_get(x_3, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_3, 0);
lean_dec(x_52);
lean_inc_ref(x_7);
x_53 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_53, 0, x_7);
lean_closure_set(x_53, 1, x_5);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_string_utf8_byte_size(x_7);
lean_inc(x_56);
lean_inc_ref(x_7);
lean_ctor_set(x_3, 2, x_56);
lean_ctor_set(x_3, 1, x_55);
lean_ctor_set(x_3, 0, x_7);
x_57 = l_Substring_nextn(x_3, x_54, x_55);
lean_dec_ref(x_3);
x_58 = lean_string_utf8_extract(x_7, x_57, x_56);
lean_dec(x_56);
lean_dec(x_57);
lean_dec_ref(x_7);
x_59 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_apply_2(x_50, lean_box(0), x_59);
x_61 = lean_apply_4(x_48, lean_box(0), lean_box(0), x_60, x_53);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_3, 2);
lean_inc(x_62);
lean_dec(x_3);
lean_inc_ref(x_7);
x_63 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_63, 0, x_7);
lean_closure_set(x_63, 1, x_5);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_string_utf8_byte_size(x_7);
lean_inc(x_66);
lean_inc_ref(x_7);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_7);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Substring_nextn(x_67, x_64, x_65);
lean_dec_ref(x_67);
x_69 = lean_string_utf8_extract(x_7, x_68, x_66);
lean_dec(x_66);
lean_dec(x_68);
lean_dec_ref(x_7);
x_70 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_70, 0, x_69);
x_71 = lean_apply_2(x_62, lean_box(0), x_70);
x_72 = lean_apply_4(x_48, lean_box(0), lean_box(0), x_71, x_63);
return x_72;
}
}
}
else
{
lean_object* x_73; uint32_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_string_utf8_get(x_7, x_73);
lean_dec_ref(x_7);
x_75 = lean_box_uint32(x_74);
x_76 = lean_apply_1(x_5, x_75);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_shortOption___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box_uint32(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_string_utf8_extract(x_1, x_2, x_3);
x_9 = 32;
x_10 = lean_string_utf8_byte_size(x_8);
lean_inc(x_2);
x_11 = l_String_posOfAux(x_8, x_9, x_10, x_2);
x_12 = lean_nat_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_11);
lean_inc_ref(x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_string_utf8_next(x_8, x_11);
lean_dec(x_11);
x_15 = lean_string_utf8_extract(x_8, x_14, x_10);
lean_dec(x_10);
lean_dec(x_14);
lean_dec_ref(x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_2(x_5, lean_box(0), x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_apply_1(x_4, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = 45;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_string_length(x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get(x_4, x_12);
x_15 = 61;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_apply_1(x_10, x_4);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
x_25 = lean_box_uint32(x_6);
x_26 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_9);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_string_utf8_byte_size(x_4);
lean_inc(x_28);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 2, x_28);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_4);
x_29 = l_Substring_nextn(x_2, x_12, x_27);
lean_dec_ref(x_2);
x_30 = lean_string_utf8_extract(x_4, x_29, x_28);
lean_dec(x_28);
lean_dec(x_29);
lean_dec_ref(x_4);
x_31 = lean_string_utf8_byte_size(x_30);
x_32 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_33 = l_Substring_takeWhileAux(x_30, x_31, x_32, x_27);
x_34 = lean_string_utf8_extract(x_30, x_33, x_31);
lean_dec(x_31);
lean_dec(x_33);
lean_dec_ref(x_30);
x_35 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_apply_2(x_22, lean_box(0), x_35);
x_37 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_36, x_26);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_box_uint32(x_6);
x_40 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_40, 0, x_9);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_string_utf8_byte_size(x_4);
lean_inc(x_42);
lean_inc_ref(x_4);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = l_Substring_nextn(x_43, x_12, x_41);
lean_dec_ref(x_43);
x_45 = lean_string_utf8_extract(x_4, x_44, x_42);
lean_dec(x_42);
lean_dec(x_44);
lean_dec_ref(x_4);
x_46 = lean_string_utf8_byte_size(x_45);
x_47 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_48 = l_Substring_takeWhileAux(x_45, x_46, x_47, x_41);
x_49 = lean_string_utf8_extract(x_45, x_48, x_46);
lean_dec(x_46);
lean_dec(x_48);
lean_dec_ref(x_45);
x_50 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_apply_2(x_38, lean_box(0), x_50);
x_52 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_51, x_40);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_10);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_2, 0);
lean_dec(x_57);
x_58 = lean_box_uint32(x_6);
x_59 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_59, 0, x_9);
lean_closure_set(x_59, 1, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_string_utf8_byte_size(x_4);
lean_inc(x_62);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 2, x_62);
lean_ctor_set(x_2, 1, x_61);
lean_ctor_set(x_2, 0, x_4);
x_63 = l_Substring_nextn(x_2, x_60, x_61);
lean_dec_ref(x_2);
x_64 = lean_string_utf8_extract(x_4, x_63, x_62);
lean_dec(x_62);
lean_dec(x_63);
lean_dec_ref(x_4);
x_65 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_65, 0, x_64);
x_66 = lean_apply_2(x_55, lean_box(0), x_65);
x_67 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_66, x_59);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_68 = lean_ctor_get(x_2, 2);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_box_uint32(x_6);
x_70 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_70, 0, x_9);
lean_closure_set(x_70, 1, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_string_utf8_byte_size(x_4);
lean_inc(x_73);
lean_inc_ref(x_4);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Substring_nextn(x_74, x_71, x_72);
lean_dec_ref(x_74);
x_76 = lean_string_utf8_extract(x_4, x_75, x_73);
lean_dec(x_73);
lean_dec(x_75);
lean_dec_ref(x_4);
x_77 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_77, 0, x_76);
x_78 = lean_apply_2(x_68, lean_box(0), x_77);
x_79 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_78, x_70);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = lean_box_uint32(x_6);
x_81 = lean_apply_1(x_9, x_80);
return x_81;
}
}
else
{
lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_3, 0);
lean_inc(x_82);
lean_dec_ref(x_3);
x_83 = 61;
x_84 = lean_string_utf8_byte_size(x_4);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_String_posOfAux(x_4, x_83, x_84, x_85);
x_87 = lean_nat_dec_eq(x_86, x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
lean_dec_ref(x_2);
lean_inc(x_88);
lean_inc(x_89);
lean_inc(x_86);
lean_inc_ref(x_4);
x_90 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_90, 0, x_4);
lean_closure_set(x_90, 1, x_85);
lean_closure_set(x_90, 2, x_86);
lean_closure_set(x_90, 3, x_82);
lean_closure_set(x_90, 4, x_89);
lean_closure_set(x_90, 5, x_88);
x_91 = lean_string_utf8_next(x_4, x_86);
lean_dec(x_86);
x_92 = lean_string_utf8_extract(x_4, x_91, x_84);
lean_dec(x_84);
lean_dec(x_91);
lean_dec_ref(x_4);
x_93 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_93, 0, x_92);
x_94 = lean_apply_2(x_89, lean_box(0), x_93);
x_95 = lean_apply_4(x_88, lean_box(0), lean_box(0), x_94, x_90);
return x_95;
}
else
{
uint32_t x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_86);
x_96 = 32;
x_97 = l_String_posOfAux(x_4, x_96, x_84, x_85);
x_98 = lean_nat_dec_eq(x_97, x_84);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
lean_dec_ref(x_2);
lean_inc(x_97);
lean_inc_ref(x_4);
x_101 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_101, 0, x_4);
lean_closure_set(x_101, 1, x_85);
lean_closure_set(x_101, 2, x_97);
lean_closure_set(x_101, 3, x_82);
x_102 = lean_string_utf8_next(x_4, x_97);
lean_dec(x_97);
x_103 = lean_string_utf8_extract(x_4, x_102, x_84);
lean_dec(x_84);
lean_dec(x_102);
lean_dec_ref(x_4);
x_104 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_104, 0, x_103);
x_105 = lean_apply_2(x_100, lean_box(0), x_104);
x_106 = lean_apply_4(x_99, lean_box(0), lean_box(0), x_105, x_101);
return x_106;
}
else
{
lean_object* x_107; 
lean_dec(x_97);
lean_dec(x_84);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = lean_apply_1(x_82, x_4);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_string_utf8_get(x_6, x_7);
x_9 = 45;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_string_length(x_6);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint32_t x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_string_utf8_get(x_6, x_14);
x_17 = 61;
x_18 = lean_uint32_dec_eq(x_16, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 32;
x_20 = lean_uint32_dec_eq(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_21 = lean_apply_1(x_12, x_6);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_12);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_box_uint32(x_8);
x_28 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_28, 0, x_11);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_string_utf8_byte_size(x_6);
lean_inc(x_30);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 2, x_30);
lean_ctor_set(x_3, 1, x_29);
lean_ctor_set(x_3, 0, x_6);
x_31 = l_Substring_nextn(x_3, x_14, x_29);
lean_dec_ref(x_3);
x_32 = lean_string_utf8_extract(x_6, x_31, x_30);
lean_dec(x_30);
lean_dec(x_31);
lean_dec_ref(x_6);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_35 = l_Substring_takeWhileAux(x_32, x_33, x_34, x_29);
x_36 = lean_string_utf8_extract(x_32, x_35, x_33);
lean_dec(x_33);
lean_dec(x_35);
lean_dec_ref(x_32);
x_37 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_apply_2(x_24, lean_box(0), x_37);
x_39 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_38, x_28);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_3, 2);
lean_inc(x_40);
lean_dec(x_3);
x_41 = lean_box_uint32(x_8);
x_42 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_42, 0, x_11);
lean_closure_set(x_42, 1, x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_string_utf8_byte_size(x_6);
lean_inc(x_44);
lean_inc_ref(x_6);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Substring_nextn(x_45, x_14, x_43);
lean_dec_ref(x_45);
x_47 = lean_string_utf8_extract(x_6, x_46, x_44);
lean_dec(x_44);
lean_dec(x_46);
lean_dec_ref(x_6);
x_48 = lean_string_utf8_byte_size(x_47);
x_49 = l_Lake_shortOptionWithSpace___redArg___closed__0;
x_50 = l_Substring_takeWhileAux(x_47, x_48, x_49, x_43);
x_51 = lean_string_utf8_extract(x_47, x_50, x_48);
lean_dec(x_48);
lean_dec(x_50);
lean_dec_ref(x_47);
x_52 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_52, 0, x_51);
x_53 = lean_apply_2(x_40, lean_box(0), x_52);
x_54 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_53, x_42);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_12);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_3, 2);
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 0);
lean_dec(x_59);
x_60 = lean_box_uint32(x_8);
x_61 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_61, 0, x_11);
lean_closure_set(x_61, 1, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_string_utf8_byte_size(x_6);
lean_inc(x_64);
lean_inc_ref(x_6);
lean_ctor_set(x_3, 2, x_64);
lean_ctor_set(x_3, 1, x_63);
lean_ctor_set(x_3, 0, x_6);
x_65 = l_Substring_nextn(x_3, x_62, x_63);
lean_dec_ref(x_3);
x_66 = lean_string_utf8_extract(x_6, x_65, x_64);
lean_dec(x_64);
lean_dec(x_65);
lean_dec_ref(x_6);
x_67 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_apply_2(x_57, lean_box(0), x_67);
x_69 = lean_apply_4(x_55, lean_box(0), lean_box(0), x_68, x_61);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_70 = lean_ctor_get(x_3, 2);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_box_uint32(x_8);
x_72 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_72, 0, x_11);
lean_closure_set(x_72, 1, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_string_utf8_byte_size(x_6);
lean_inc(x_75);
lean_inc_ref(x_6);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
x_77 = l_Substring_nextn(x_76, x_73, x_74);
lean_dec_ref(x_76);
x_78 = lean_string_utf8_extract(x_6, x_77, x_75);
lean_dec(x_75);
lean_dec(x_77);
lean_dec_ref(x_6);
x_79 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_apply_2(x_70, lean_box(0), x_79);
x_81 = lean_apply_4(x_55, lean_box(0), lean_box(0), x_80, x_72);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_82 = lean_box_uint32(x_8);
x_83 = lean_apply_1(x_11, x_82);
return x_83;
}
}
else
{
lean_object* x_84; uint32_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
lean_dec_ref(x_5);
x_85 = 61;
x_86 = lean_string_utf8_byte_size(x_6);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_String_posOfAux(x_6, x_85, x_86, x_87);
x_89 = lean_nat_dec_eq(x_88, x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
lean_dec_ref(x_2);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
lean_dec_ref(x_3);
lean_inc(x_90);
lean_inc(x_91);
lean_inc(x_88);
lean_inc_ref(x_6);
x_92 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_92, 0, x_6);
lean_closure_set(x_92, 1, x_87);
lean_closure_set(x_92, 2, x_88);
lean_closure_set(x_92, 3, x_84);
lean_closure_set(x_92, 4, x_91);
lean_closure_set(x_92, 5, x_90);
x_93 = lean_string_utf8_next(x_6, x_88);
lean_dec(x_88);
x_94 = lean_string_utf8_extract(x_6, x_93, x_86);
lean_dec(x_86);
lean_dec(x_93);
lean_dec_ref(x_6);
x_95 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_95, 0, x_94);
x_96 = lean_apply_2(x_91, lean_box(0), x_95);
x_97 = lean_apply_4(x_90, lean_box(0), lean_box(0), x_96, x_92);
return x_97;
}
else
{
uint32_t x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_88);
x_98 = 32;
x_99 = l_String_posOfAux(x_6, x_98, x_86, x_87);
x_100 = lean_nat_dec_eq(x_99, x_86);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
lean_dec_ref(x_2);
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
lean_dec_ref(x_3);
lean_inc(x_99);
lean_inc_ref(x_6);
x_103 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_103, 0, x_6);
lean_closure_set(x_103, 1, x_87);
lean_closure_set(x_103, 2, x_99);
lean_closure_set(x_103, 3, x_84);
x_104 = lean_string_utf8_next(x_6, x_99);
lean_dec(x_99);
x_105 = lean_string_utf8_extract(x_6, x_104, x_86);
lean_dec(x_86);
lean_dec(x_104);
lean_dec_ref(x_6);
x_106 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_106, 0, x_105);
x_107 = lean_apply_2(x_102, lean_box(0), x_106);
x_108 = lean_apply_4(x_101, lean_box(0), lean_box(0), x_107, x_103);
return x_108;
}
else
{
lean_object* x_109; 
lean_dec(x_99);
lean_dec(x_86);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_109 = lean_apply_1(x_84, x_6);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lake_option___redArg___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_option___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_option___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_option___redArg___lam__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_string_length(x_8);
x_19 = lean_nat_dec_lt(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_8);
x_11 = x_19;
goto block_16;
}
else
{
lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_get(x_8, x_20);
lean_dec(x_8);
x_22 = 45;
x_23 = lean_uint32_dec_eq(x_21, x_22);
x_11 = x_23;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_apply_1(x_3, x_9);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_10);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1), 5, 4);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOption___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOptions___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_24; uint8_t x_25; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec_ref(x_7);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2), 5, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_string_length(x_10);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_lt(x_24, x_13);
if (x_25 == 0)
{
lean_dec(x_10);
x_14 = x_25;
goto block_23;
}
else
{
lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_get(x_10, x_26);
lean_dec(x_10);
x_28 = 45;
x_29 = lean_uint32_dec_eq(x_27, x_28);
x_14 = x_29;
goto block_23;
}
block_23:
{
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_apply_1(x_5, x_11);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_6);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_apply_1(x_5, x_11);
x_22 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_21, x_12);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_inc_ref(x_9);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1), 7, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_7);
lean_closure_set(x_10, 5, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOptions___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_collectArgs___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_9 = lean_apply_2(x_1, lean_box(0), x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_string_length(x_10);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_lt(x_21, x_11);
if (x_22 == 0)
{
x_12 = x_22;
goto block_20;
}
else
{
lean_object* x_23; uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_string_utf8_get(x_10, x_23);
x_25 = 45;
x_26 = lean_uint32_dec_eq(x_24, x_25);
x_12 = x_26;
goto block_20;
}
block_20:
{
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_2, x_10);
x_16 = l_Lake_collectArgs___redArg(x_3, x_4, x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = l_Lake_collectArgs___redArg(x_3, x_4, x_5, x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_18 = lean_apply_1(x_5, x_10);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__0), 1, 0);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_inc(x_7);
x_11 = lean_apply_2(x_7, lean_box(0), x_9);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2), 8, 7);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_10);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_collectArgs___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_array_to_list(x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_processOptions___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lake_processOptions___redArg___closed__0;
x_7 = l_Lake_collectArgs___redArg(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_Lake_processOptions___redArg___closed__0;
x_8 = l_Lake_collectArgs___redArg(x_2, x_3, x_4, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
lean_object* initialize_Init_Control_State(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Cli(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_shortOptionWithSpace___redArg___closed__0 = _init_l_Lake_shortOptionWithSpace___redArg___closed__0();
lean_mark_persistent(l_Lake_shortOptionWithSpace___redArg___closed__0);
l_Lake_processOptions___redArg___closed__0 = _init_l_Lake_processOptions___redArg___closed__0();
lean_mark_persistent(l_Lake_processOptions___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
