// Lean compiler output
// Module: Lean.Util.SafeExponentiation
// Imports: Lean.CoreM
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
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_checkExponent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2;
lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_checkExponent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_checkExponent___closed__8;
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7;
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5;
lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_40____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__2;
static lean_object* l_Lean_checkExponent___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_checkExponent___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_object*);
static lean_object* l_Lean_checkExponent___closed__10;
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__2___boxed(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__7;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__9;
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4;
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__4;
static lean_object* l_Lean_checkExponent___closed__6;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exponentiation_threshold;
LEAN_EXPORT uint8_t l_Lean_checkExponent___lambda__2(lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exponentiation", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum value for which exponentiation operations are safe to evaluate. When an exponent is a value greater than this threshold, the exponentiation will not be evaluated, and a warning will be logged. This helps to prevent the system from becoming unresponsive due to excessively large computations.", 299, 299);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4;
x_3 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7;
x_2 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3;
x_3 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6;
x_4 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_40____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_checkExponent___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1;
x_7 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_1, x_8, x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 2;
x_11 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_checkExponent___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_exponentiation_threshold;
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsafe", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_checkExponent___closed__2;
x_2 = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_checkExponent___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exponent ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" exceeds the threshold ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", exponentiation operation was not evaluated, use `set_option ", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_checkExponent___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_exponentiation_threshold;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_checkExponent___closed__8;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <num>` to set a new threshold", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_checkExponent___closed__1;
x_7 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = l_Lean_checkExponent___closed__3;
x_13 = l_Lean_logMessageKind(x_12, x_2, x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_checkExponent___closed__4;
x_17 = lean_unbox(x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_apply_4(x_16, x_18, x_2, x_3, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_21 = l_Lean_checkExponent___closed__5;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_checkExponent___closed__6;
x_24 = lean_string_append(x_22, x_23);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Lean_checkExponent___closed__7;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_checkExponent___closed__9;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_checkExponent___closed__10;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
lean_inc(x_2);
x_35 = l_Lean_logWarning___at_Lean_checkExponent___spec__1(x_34, x_2, x_3, x_15);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_apply_4(x_16, x_36, x_2, x_3, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_checkExponent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at_Lean_checkExponent___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_checkExponent___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_checkExponent___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__1);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__2);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__3);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__4);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__5);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__6);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__7);
l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8 = _init_l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5____closed__8);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_exponentiation_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exponentiation_threshold);
lean_dec_ref(res);
}l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1 = _init_l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_checkExponent___spec__1___closed__1);
l_Lean_checkExponent___closed__1 = _init_l_Lean_checkExponent___closed__1();
lean_mark_persistent(l_Lean_checkExponent___closed__1);
l_Lean_checkExponent___closed__2 = _init_l_Lean_checkExponent___closed__2();
lean_mark_persistent(l_Lean_checkExponent___closed__2);
l_Lean_checkExponent___closed__3 = _init_l_Lean_checkExponent___closed__3();
lean_mark_persistent(l_Lean_checkExponent___closed__3);
l_Lean_checkExponent___closed__4 = _init_l_Lean_checkExponent___closed__4();
lean_mark_persistent(l_Lean_checkExponent___closed__4);
l_Lean_checkExponent___closed__5 = _init_l_Lean_checkExponent___closed__5();
lean_mark_persistent(l_Lean_checkExponent___closed__5);
l_Lean_checkExponent___closed__6 = _init_l_Lean_checkExponent___closed__6();
lean_mark_persistent(l_Lean_checkExponent___closed__6);
l_Lean_checkExponent___closed__7 = _init_l_Lean_checkExponent___closed__7();
lean_mark_persistent(l_Lean_checkExponent___closed__7);
l_Lean_checkExponent___closed__8 = _init_l_Lean_checkExponent___closed__8();
lean_mark_persistent(l_Lean_checkExponent___closed__8);
l_Lean_checkExponent___closed__9 = _init_l_Lean_checkExponent___closed__9();
lean_mark_persistent(l_Lean_checkExponent___closed__9);
l_Lean_checkExponent___closed__10 = _init_l_Lean_checkExponent___closed__10();
lean_mark_persistent(l_Lean_checkExponent___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
