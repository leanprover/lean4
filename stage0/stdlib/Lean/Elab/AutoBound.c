// Lean compiler output
// Module: Lean.Elab.AutoBound
// Imports: Lean.Data.Options
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
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundImplicitName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_;
static lean_object* l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_;
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_40_(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_;
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_;
static lean_object* l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_;
static lean_object* l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_autoImplicit;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_relaxedAutoImplicit;
static lean_object* l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_;
static lean_object* l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isValidAutoBoundImplicitName(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_;
LEAN_EXPORT lean_object* l_Lean_Elab_isValidAutoBoundLevelName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoImplicit", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unbound local variables in declaration headers become implicit arguments. In \"relaxed\" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}.", 322, 319);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_;
x_2 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_;
x_2 = l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_;
x_3 = l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_;
x_3 = l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_;
x_4 = l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_;
x_5 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("relaxedAutoImplicit", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see option `autoImplicit`).", 134, 134);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_;
x_2 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_;
x_2 = l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_;
x_3 = l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_;
x_3 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_;
x_4 = l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_;
x_5 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_nat_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_18; uint8_t x_19; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_18 = 48;
x_19 = lean_uint32_dec_le(x_18, x_10);
if (x_19 == 0)
{
x_11 = x_19;
goto block_17;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 57;
x_21 = lean_uint32_dec_le(x_10, x_20);
x_11 = x_21;
goto block_17;
}
block_17:
{
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_10);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 95;
x_14 = lean_uint32_dec_eq(x_10, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 39;
x_16 = lean_uint32_dec_eq(x_10, x_15);
x_8 = x_16;
goto block_9;
}
else
{
x_8 = x_14;
goto block_9;
}
}
else
{
goto block_6;
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
block_9:
{
if (x_8 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Substring_nextn(x_4, x_5, x_2);
lean_dec(x_4);
x_7 = l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(x_1, x_3, x_6);
lean_dec(x_3);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at_____private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(x_1, x_2, x_3);
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
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_length(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_7;
}
else
{
if (x_2 == 0)
{
uint8_t x_8; 
x_8 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_4);
return x_8;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_length(x_4);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_4);
return x_10;
}
else
{
if (x_2 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_4, x_8);
x_12 = 97;
x_13 = lean_uint32_dec_le(x_12, x_11);
if (x_13 == 0)
{
x_5 = x_13;
goto block_7;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 122;
x_15 = lean_uint32_dec_le(x_11, x_14);
x_5 = x_15;
goto block_7;
}
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
block_7:
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(x_4);
return x_6;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
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
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_AutoBound___hyg_6_);
l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_ = _init_l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_AutoBound___hyg_6_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoImplicit);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_AutoBound___hyg_40_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_AutoBound___hyg_40_);
l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_ = _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_AutoBound___hyg_40_);
l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_ = _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_AutoBound___hyg_40_);
l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_ = _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_AutoBound___hyg_40_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_relaxedAutoImplicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_relaxedAutoImplicit);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
