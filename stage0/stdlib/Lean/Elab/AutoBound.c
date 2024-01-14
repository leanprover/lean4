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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7_(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3;
LEAN_EXPORT lean_object* l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41_(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_autoImplicit;
LEAN_EXPORT lean_object* l_Lean_Elab_relaxedAutoImplicit;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object*, uint8_t);
uint8_t l_Char_isLower(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("autoImplicit", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unbound local variables in declaration headers become implicit arguments. In \"relaxed\" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}.", 322);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("relaxedAutoImplicit", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see optin `autoBoundImplicitLocal`.", 142);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_Char_isDigit(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_isSubScriptAlnum(x_6);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 95;
x_10 = lean_uint32_dec_eq(x_6, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 39;
x_12 = lean_uint32_dec_eq(x_6, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
x_16 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
x_20 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
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
x_8 = l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1(x_1, x_2, x_7);
lean_dec(x_2);
lean_dec(x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_string_length(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
if (x_2 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_4);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Elab_isValidAutoBoundImplicitName(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_string_length(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
if (x_2 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get(x_4, x_6);
x_10 = l_Char_isLower(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_4);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = 1;
return x_13;
}
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Elab_isValidAutoBoundLevelName(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____closed__8);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoImplicit);
lean_dec_ref(res);
}l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41____closed__5);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_41_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_relaxedAutoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_relaxedAutoImplicit);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
