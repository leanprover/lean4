// Lean compiler output
// Module: Lean.Util.Profile
// Imports: Init Lean.Data.Options
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
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler;
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2;
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_profiler_threshold_getSecs___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4;
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static double l_Lean_profiler_threshold_getSecs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_get_profiler(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT double lean_get_profiler_threshold(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object*);
static lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1;
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5;
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
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
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("profiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("show execution times of various Lean components", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5;
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4;
x_4 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc(x_7);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("threshold", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("threshold in milliseconds, profiling times under threshold will not be reported individually", 92);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5;
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Profile___hyg_41_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4;
x_4 = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_41____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
LEAN_EXPORT uint8_t lean_get_profiler(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_get_profiler(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_profiler_threshold_getSecs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_profiler_threshold_getSecs___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT double lean_get_profiler_threshold(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; double x_6; double x_7; double x_8; 
x_2 = l_Lean_profiler_threshold_getSecs___closed__1;
x_3 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Float_ofScientific(x_3, x_4, x_5);
lean_dec(x_3);
x_7 = l_Lean_profiler_threshold_getSecs___closed__2;
x_8 = lean_float_div(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_get_profiler_threshold(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_profileit(x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_profileit(x_1, x_2, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_profileitIOUnsafe___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_5, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_profileitM___rarg___lambda__1___boxed), 6, 3);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_profileitM___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_profileitM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__1);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__2);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__3);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__4);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__5);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_6____closed__6);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_Profile___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__1);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__2);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__3);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__4);
l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_Profile___hyg_41____closed__5);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_Profile___hyg_41_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler_threshold);
lean_dec_ref(res);
}l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1 = _init_l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1();
lean_mark_persistent(l___private_Lean_Util_Profile_0__Lean_get__profiler___closed__1);
l_Lean_profiler_threshold_getSecs___closed__1 = _init_l_Lean_profiler_threshold_getSecs___closed__1();
lean_mark_persistent(l_Lean_profiler_threshold_getSecs___closed__1);
l_Lean_profiler_threshold_getSecs___closed__2 = _init_l_Lean_profiler_threshold_getSecs___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
