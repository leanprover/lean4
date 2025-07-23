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
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_;
static lean_object* l_Lean_checkExponent___closed__2;
static lean_object* l_Lean_checkExponent___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_checkExponent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_;
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_;
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkExponent___lam__0___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_checkExponent___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_object*);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_;
LEAN_EXPORT uint8_t l_Lean_checkExponent___lam__0(lean_object*);
static lean_object* l_Lean_checkExponent___closed__0;
lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_checkExponent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_checkExponent___closed__4;
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_;
static lean_object* l_Lean_checkExponent___closed__6;
LEAN_EXPORT lean_object* l_Lean_exponentiation_threshold;
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exponentiation", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum value for which exponentiation operations are safe to evaluate. When an exponent is a value greater than this threshold, the exponentiation will not be evaluated, and a warning will be logged. This helps to prevent the system from becoming unresponsive due to excessively large computations.", 299, 299);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_2 = l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_3 = lean_unsigned_to_nat(256u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_3 = l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_3 = l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_4 = l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_checkExponent_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 1;
x_6 = 0;
x_7 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__23_spec__23(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_checkExponent___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_exponentiation_threshold;
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsafe", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_;
x_2 = l_Lean_checkExponent___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exponent ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" exceeds the threshold ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", exponentiation operation was not evaluated, use `set_option ", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_checkExponent___closed__6() {
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
lean_object* x_5; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = l_Lean_checkExponent___closed__0;
x_12 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_10, x_11);
lean_dec(x_10);
x_13 = lean_nat_dec_lt(x_12, x_1);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_checkExponent___closed__2;
x_18 = l_Lean_logMessageKind___redArg(x_17, x_3, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_5 = x_21;
goto block_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Lean_checkExponent___lam__0___boxed), 1, 0);
x_25 = l_Lean_checkExponent___closed__3;
x_26 = l_Nat_reprFast(x_1);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = l_Lean_checkExponent___closed__4;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Nat_reprFast(x_12);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l_Lean_checkExponent___closed__5;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_unbox(x_19);
lean_dec(x_19);
x_35 = l_Lean_Name_toString(x_23, x_34, x_24);
x_36 = lean_string_append(x_33, x_35);
lean_dec_ref(x_35);
x_37 = l_Lean_checkExponent___closed__6;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = l_Lean_logWarning___at___Lean_checkExponent_spec__0(x_40, x_2, x_3, x_22);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_5 = x_42;
goto block_9;
}
}
block_9:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_checkExponent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at___Lean_checkExponent_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_checkExponent___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_checkExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_checkExponent(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Util_SafeExponentiation___hyg_5_);
l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_ = _init_l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Util_SafeExponentiation___hyg_5_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_SafeExponentiation___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_exponentiation_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_exponentiation_threshold);
lean_dec_ref(res);
}l_Lean_checkExponent___closed__0 = _init_l_Lean_checkExponent___closed__0();
lean_mark_persistent(l_Lean_checkExponent___closed__0);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
