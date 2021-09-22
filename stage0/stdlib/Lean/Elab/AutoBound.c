// Lean compiler output
// Module: Lean.Elab.AutoBound
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
static lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object*);
uint8_t l_String_anyAux_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_autoBoundImplicitLocal;
uint8_t l_Char_isDigit(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5;
uint8_t l_Char_isLower(uint32_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1;
static lean_object* l_Lean_Elab_autoBoundImplicitLocal___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object*);
uint8_t l_Lean_isGreek(uint32_t);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_alloc_ctor(1, 0, 1);
x_8 = lean_unbox(x_4);
lean_ctor_set_uint8(x_7, 0, x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_4);
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
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoBoundImplicitLocal");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unbound local variables in declaration headers become implicit arguments if they are a lower case or greek letter followed by numeric digits. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}.");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_autoBoundImplicitLocal___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isDigit(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_isSubScriptAlnum(x_1);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 95;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 39;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
static lean_object* _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Substring_nextn(x_4, x_5, x_3);
lean_dec(x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
x_8 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1;
x_9 = l_String_anyAux_loop(x_1, x_2, x_8, x_7);
lean_dec(x_2);
lean_dec(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_length(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_string_utf8_get(x_3, x_5);
x_9 = l_Lean_isGreek(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isLower(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_3);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_3);
return x_13;
}
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isValidAutoBoundImplicitName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_length(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_string_utf8_get(x_3, x_5);
x_9 = l_Char_isLower(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_3);
return x_11;
}
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isValidAutoBoundLevelName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Options(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AutoBound(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____closed__5);
l_Lean_Elab_autoBoundImplicitLocal___closed__1 = _init_l_Lean_Elab_autoBoundImplicitLocal___closed__1();
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitLocal___closed__1);
res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoBoundImplicitLocal = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitLocal);
lean_dec_ref(res);
l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1 = _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1();
lean_mark_persistent(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
